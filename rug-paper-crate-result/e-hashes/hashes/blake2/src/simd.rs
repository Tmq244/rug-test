// Copyright 2015 blake2-rfc Developers
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

mod simd_opt;
mod simdint;
mod simdop;
mod simdty;

pub use self::simdty::{u32x4, u64x4};

pub trait Vector4<T>: Copy {
    fn gather(src: &[T], i0: usize, i1: usize, i2: usize, i3: usize) -> Self;

    #[allow(clippy::wrong_self_convention)]
    fn from_le(self) -> Self;
    fn to_le(self) -> Self;

    fn wrapping_add(self, rhs: Self) -> Self;

    fn rotate_right_const(self, n: u32) -> Self;

    fn shuffle_left_1(self) -> Self;
    fn shuffle_left_2(self) -> Self;
    fn shuffle_left_3(self) -> Self;

    #[inline(always)]
    fn shuffle_right_1(self) -> Self {
        self.shuffle_left_3()
    }
    #[inline(always)]
    fn shuffle_right_2(self) -> Self {
        self.shuffle_left_2()
    }
    #[inline(always)]
    fn shuffle_right_3(self) -> Self {
        self.shuffle_left_1()
    }
}

macro_rules! impl_vector4 {
    ($vec:ident, $word:ident) => {
        impl Vector4<$word> for $vec {
            #[inline(always)]
            fn gather(src: &[$word], i0: usize, i1: usize, i2: usize, i3: usize) -> Self {
                $vec::new(src[i0], src[i1], src[i2], src[i3])
            }

            #[cfg(target_endian = "little")]
            #[inline(always)]
            fn from_le(self) -> Self {
                self
            }

            #[cfg(not(target_endian = "little"))]
            #[inline(always)]
            fn from_le(self) -> Self {
                $vec::new(
                    $word::from_le(self.0),
                    $word::from_le(self.1),
                    $word::from_le(self.2),
                    $word::from_le(self.3),
                )
            }

            #[cfg(target_endian = "little")]
            #[inline(always)]
            fn to_le(self) -> Self {
                self
            }

            #[cfg(not(target_endian = "little"))]
            #[inline(always)]
            fn to_le(self) -> Self {
                $vec::new(
                    self.0.to_le(),
                    self.1.to_le(),
                    self.2.to_le(),
                    self.3.to_le(),
                )
            }

            #[inline(always)]
            fn wrapping_add(self, rhs: Self) -> Self {
                self + rhs
            }

            #[inline(always)]
            fn rotate_right_const(self, n: u32) -> Self {
                simd_opt::$vec::rotate_right_const(self, n)
            }

            #[cfg(feature = "simd")]
            #[inline(always)]
            fn shuffle_left_1(self) -> Self {
                use crate::simd::simdint::simd_shuffle4;
                const IDX: [u32; 4] = [1, 2, 3, 0];
                unsafe { simd_shuffle4(self, self, IDX) }
            }

            #[cfg(not(feature = "simd"))]
            #[inline(always)]
            fn shuffle_left_1(self) -> Self {
                $vec::new(self.1, self.2, self.3, self.0)
            }

            #[cfg(feature = "simd")]
            #[inline(always)]
            fn shuffle_left_2(self) -> Self {
                use crate::simd::simdint::simd_shuffle4;
                const IDX: [u32; 4] = [2, 3, 0, 1];
                unsafe { simd_shuffle4(self, self, IDX) }
            }

            #[cfg(not(feature = "simd"))]
            #[inline(always)]
            fn shuffle_left_2(self) -> Self {
                $vec::new(self.2, self.3, self.0, self.1)
            }

            #[cfg(feature = "simd")]
            #[inline(always)]
            fn shuffle_left_3(self) -> Self {
                use crate::simd::simdint::simd_shuffle4;
                const IDX: [u32; 4] = [3, 0, 1, 2];
                unsafe { simd_shuffle4(self, self, IDX) }
            }

            #[cfg(not(feature = "simd"))]
            #[inline(always)]
            fn shuffle_left_3(self) -> Self {
                $vec::new(self.3, self.0, self.1, self.2)
            }
        }
    };
}

impl_vector4!(u32x4, u32);
impl_vector4!(u64x4, u64);
#[cfg(test)]
mod tests_rug_41 {
    use super::*;
    use crate::simd::Vector4;

    // Mock implementation of Vector4 for testing purposes
    #[derive(Copy, Clone)]
    struct TestVector4([u32; 4]);

    impl Vector4<u32> for TestVector4 {
        fn gather(src: &[u32], i0: usize, i1: usize, i2: usize, i3: usize) -> Self {
            TestVector4([src[i0], src[i1], src[i2], src[i3]])
        }

        fn from_le(self) -> Self {
            self
        }

        fn to_le(self) -> Self {
            self
        }

        fn wrapping_add(self, rhs: Self) -> Self {
            TestVector4([
                self.0[0].wrapping_add(rhs.0[0]),
                self.0[1].wrapping_add(rhs.0[1]),
                self.0[2].wrapping_add(rhs.0[2]),
                self.0[3].wrapping_add(rhs.0[3]),
            ])
        }

        fn rotate_right_const(self, n: u32) -> Self {
            TestVector4([
                self.0[0].rotate_right(n),
                self.0[1].rotate_right(n),
                self.0[2].rotate_right(n),
                self.0[3].rotate_right(n),
            ])
        }

        fn shuffle_left_1(self) -> Self {
            TestVector4([self.0[1], self.0[2], self.0[3], self.0[0]])
        }

        fn shuffle_left_2(self) -> Self {
            TestVector4([self.0[2], self.0[3], self.0[0], self.0[1]])
        }

        fn shuffle_left_3(self) -> Self {
            TestVector4([self.0[3], self.0[0], self.0[1], self.0[2]])
        }
    }

    #[test]
    fn test_shuffle_right_1() {
        let src = [1, 2, 3, 4];
        let p0: TestVector4 = TestVector4::gather(&src, 0, 1, 2, 3);

        let result = p0.shuffle_right_1();

        assert_eq!(result.0, [4, 1, 2, 3]);
    }
}#[cfg(test)]
mod tests_rug_42 {
    use super::*;
    use crate::simd::Vector4;

    // A simple implementation of the Vector4 trait for testing purposes.
    #[derive(Copy, Clone)]
    struct TestVector4([u32; 4]);

    impl Vector4<u32> for TestVector4 {
        fn gather(src: &[u32], i0: usize, i1: usize, i2: usize, i3: usize) -> Self {
            TestVector4([src[i0], src[i1], src[i2], src[i3]])
        }

        fn from_le(self) -> Self {
            self
        }
        
        fn to_le(self) -> Self {
            self
        }
        
        fn wrapping_add(self, rhs: Self) -> Self {
            TestVector4([
                self.0[0].wrapping_add(rhs.0[0]),
                self.0[1].wrapping_add(rhs.0[1]),
                self.0[2].wrapping_add(rhs.0[2]),
                self.0[3].wrapping_add(rhs.0[3]),
            ])
        }
        
        fn rotate_right_const(self, n: u32) -> Self {
            TestVector4([
                self.0[0].rotate_right(n),
                self.0[1].rotate_right(n),
                self.0[2].rotate_right(n),
                self.0[3].rotate_right(n),
            ])
        }
        
        fn shuffle_left_1(self) -> Self {
            TestVector4([self.0[1], self.0[2], self.0[3], self.0[0]])
        }
        
        fn shuffle_left_2(self) -> Self {
            TestVector4([self.0[2], self.0[3], self.0[0], self.0[1]])
        }
        
        fn shuffle_left_3(self) -> Self {
            TestVector4([self.0[3], self.0[0], self.0[1], self.0[2]])
        }
    }

    #[test]
    fn test_shuffle_right_2() {
        let mut p0: TestVector4 = TestVector4([1, 2, 3, 4]);

        let shuffled = p0.shuffle_right_2();
        assert_eq!(shuffled.0, [3, 4, 1, 2]);
    }
}#[cfg(test)]
mod tests_rug_43 {
    use super::*;
    use crate::simd::Vector4;

    // Assuming a concrete implementation of Vector4 for u32 that satisfies the bounds.
    #[derive(Copy, Clone)]
    struct ConcreteVector4([u32; 4]);

    impl Vector4<u32> for ConcreteVector4 {
        fn gather(src: &[u32], i0: usize, i1: usize, i2: usize, i3: usize) -> Self {
            ConcreteVector4([src[i0], src[i1], src[i2], src[i3]])
        }

        #[allow(clippy::wrong_self_convention)]
        fn from_le(self) -> Self { self }
        fn to_le(self) -> Self { self }

        fn wrapping_add(self, rhs: Self) -> Self {
            ConcreteVector4([
                self.0[0].wrapping_add(rhs.0[0]),
                self.0[1].wrapping_add(rhs.0[1]),
                self.0[2].wrapping_add(rhs.0[2]),
                self.0[3].wrapping_add(rhs.0[3]),
            ])
        }

        fn rotate_right_const(self, n: u32) -> Self {
            ConcreteVector4([
                self.0[0].rotate_right(n),
                self.0[1].rotate_right(n),
                self.0[2].rotate_right(n),
                self.0[3].rotate_right(n),
            ])
        }

        fn shuffle_left_1(self) -> Self {
            ConcreteVector4([self.0[1], self.0[2], self.0[3], self.0[0]])
        }

        fn shuffle_left_2(self) -> Self {
            ConcreteVector4([self.0[2], self.0[3], self.0[0], self.0[1]])
        }

        fn shuffle_left_3(self) -> Self {
            ConcreteVector4([self.0[3], self.0[0], self.0[1], self.0[2]])
        }
    }

    #[test]
    fn test_shuffle_right_3() {
        let mut p0: ConcreteVector4 = ConcreteVector4::gather(&[1, 2, 3, 4], 0, 1, 2, 3);

        let result = p0.shuffle_right_3();

        assert_eq!(result.0, [2, 3, 4, 1]);
    }
}#[cfg(test)]
mod tests_rug_45 {
    use super::*;
    use crate::simd::Vector4;
    use crate::simd::simdty::Simd4;

    #[test]
    fn test_rug() {
        let mut p0 = Simd4::<u32>::new(1, 2, 3, 4);

        <Simd4<u32>>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_46 {
    use super::*;
    use crate::simd::Vector4;
    use crate::simd::simdty::Simd4;

    #[test]
    fn test_rug() {
        let mut p0: Simd4<u32> = Simd4::new(1, 2, 3, 4);

        <Simd4<u32> as Vector4<u32>>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_48 {
    use super::*;
    use crate::simd::{Vector4, simdty::Simd4};

    #[test]
    fn test_rotate_right_const() {
        let mut p0 = Simd4::<u32>::new(1, 2, 3, 4);
        let mut p1 = 2u32;

        let result = <Simd4<u32>>::rotate_right_const(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_49 {
    use super::*;
    use crate::simd::{Vector4, simdty::Simd4};

    #[test]
    fn test_rug() {
        let mut p0: Simd4<u32> = Simd4::new(1, 2, 3, 4);

        p0.shuffle_left_1();
    }
}#[cfg(test)]
mod tests_rug_51 {
    use super::*;
    use crate::simd::{Vector4, simdty::Simd4};

    #[test]
    fn test_rug() {
        let mut p0 = Simd4::<u32>::new(1, 2, 3, 4);

        let result = <Simd4<u32> as Vector4<u32>>::shuffle_left_3(p0);
        
        assert_eq!(result.0, 4);
        assert_eq!(result.1, 1);
        assert_eq!(result.2, 2);
        assert_eq!(result.3, 3);
    }
}#[cfg(test)]
mod tests_rug_52 {
    use super::*;
    use crate::simd::{Vector4, simdty::Simd4};

    #[test]
    fn test_rug() {
        let mut p0: [u64; 5] = [1, 2, 3, 4, 5];
        let mut p1: usize = 0;
        let mut p2: usize = 1;
        let mut p3: usize = 2;
        let mut p4: usize = 3;

        let result: Simd4<u64> = <Simd4<u64>>::gather(&p0, p1, p2, p3, p4);
    }
}#[cfg(test)]
mod tests_rug_53 {
    use super::*;
    use crate::simd::{Vector4, simdty::Simd4};

    #[test]
    fn test_rug() {
        let mut p0: Simd4<u64> = Simd4(1, 2, 3, 4);

        p0.from_le();
    }
}#[cfg(test)]
mod tests_rug_55 {
    use super::*;
    use crate::simd::{Vector4, simdty::Simd4};

    #[test]
    fn test_rug() {
        let mut p0 = Simd4::<u64>::new(1, 2, 3, 4);
        let mut p1 = Simd4::<u64>::new(5, 6, 7, 8);

        <Simd4<u64>>::wrapping_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_56 {
    use super::*;
    use crate::simd::Vector4;
    use crate::simd::simdty::Simd4;
    use crate::simd::simd_opt;

    #[test]
    fn test_rug() {
        let mut p0: Simd4<u64> = Simd4::new(1, 2, 3, 4);
        let mut p1: u32 = 8;

        let result = p0.rotate_right_const(p1);

        // You can add assertions here to verify the result if needed
    }
}#[cfg(test)]
mod tests_rug_57 {
    use super::*;
    use crate::simd::{Vector4, simdty::Simd4};

    #[test]
    fn test_rug() {
        let mut p0: Simd4<u64> = Simd4::new(1, 2, 3, 4);

        let shuffled = p0.shuffle_left_1();

        assert_eq!(shuffled.0, 2);
        assert_eq!(shuffled.1, 3);
        assert_eq!(shuffled.2, 4);
        assert_eq!(shuffled.3, 1);
    }
}#[cfg(test)]
mod tests_rug_59 {
    use super::*;
    use crate::simd::Vector4;
    use crate::simd::simdty::Simd4;

    #[test]
    fn test_rug() {
        let mut p0: Simd4<u64> = Simd4::new(1, 2, 3, 4);

        p0.shuffle_left_3();
    }
}