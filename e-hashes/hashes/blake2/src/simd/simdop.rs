// Copyright 2015 blake2-rfc Developers
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[cfg(feature = "simd")]
use crate::simd::simdint;
use crate::simd::simdty::{u32x4, u64x4};

use core::ops::{Add, BitXor, Shl, Shr};

macro_rules! impl_ops {
    ($vec:ident) => {
        impl Add for $vec {
            type Output = Self;

            #[cfg(feature = "simd")]
            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                unsafe { simdint::simd_add(self, rhs) }
            }

            #[cfg(not(feature = "simd"))]
            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                $vec::new(
                    self.0.wrapping_add(rhs.0),
                    self.1.wrapping_add(rhs.1),
                    self.2.wrapping_add(rhs.2),
                    self.3.wrapping_add(rhs.3),
                )
            }
        }

        impl BitXor for $vec {
            type Output = Self;

            #[cfg(feature = "simd")]
            #[inline(always)]
            fn bitxor(self, rhs: Self) -> Self::Output {
                unsafe { simdint::simd_xor(self, rhs) }
            }

            #[cfg(not(feature = "simd"))]
            #[inline(always)]
            fn bitxor(self, rhs: Self) -> Self::Output {
                $vec::new(
                    self.0 ^ rhs.0,
                    self.1 ^ rhs.1,
                    self.2 ^ rhs.2,
                    self.3 ^ rhs.3,
                )
            }
        }

        impl Shl<$vec> for $vec {
            type Output = Self;

            #[cfg(feature = "simd")]
            #[inline(always)]
            fn shl(self, rhs: Self) -> Self::Output {
                unsafe { simdint::simd_shl(self, rhs) }
            }

            #[cfg(not(feature = "simd"))]
            #[inline(always)]
            fn shl(self, rhs: Self) -> Self::Output {
                $vec::new(
                    self.0 << rhs.0,
                    self.1 << rhs.1,
                    self.2 << rhs.2,
                    self.3 << rhs.3,
                )
            }
        }

        impl Shr<$vec> for $vec {
            type Output = Self;

            #[cfg(feature = "simd")]
            #[inline(always)]
            fn shr(self, rhs: Self) -> Self::Output {
                unsafe { simdint::simd_shr(self, rhs) }
            }

            #[cfg(not(feature = "simd"))]
            #[inline(always)]
            fn shr(self, rhs: Self) -> Self::Output {
                $vec::new(
                    self.0 >> rhs.0,
                    self.1 >> rhs.1,
                    self.2 >> rhs.2,
                    self.3 >> rhs.3,
                )
            }
        }
    };
}

impl_ops!(u32x4);
impl_ops!(u64x4);
#[cfg(test)]
mod tests_rug_61 {
    use super::*;
    use crate::simd::simdty::Simd4;
    use core::ops::BitXor;

    #[test]
    fn test_bitxor() {
        let mut p0 = Simd4::<u32>::new(1, 2, 3, 4);
        let mut p1 = Simd4::<u32>::new(4, 3, 2, 1);

        let result = p0.bitxor(p1);

        assert_eq!(result.0, 5);
        assert_eq!(result.1, 1);
        assert_eq!(result.2, 1);
        assert_eq!(result.3, 5);
    }
}#[cfg(test)]
mod tests_rug_64 {
    use super::*;
    use crate::simd::simdty::Simd4;
    use core::ops::Add;

    #[test]
    fn test_add() {
        let mut p0 = Simd4::<u64>::new(1, 2, 3, 4);
        let mut p1 = Simd4::<u64>::new(5, 6, 7, 8);

        let result = p0.add(p1);
        assert_eq!(result.0, 6);
        assert_eq!(result.1, 8);
        assert_eq!(result.2, 10);
        assert_eq!(result.3, 12);
    }
}#[cfg(test)]
mod tests_rug_65 {
    use super::*;
    use core::ops::BitXor;
    use crate::simd::simdty::Simd4;

    #[test]
    fn test_rug() {
        let mut p0 = Simd4::<u64>::new(1, 2, 3, 4);
        let mut p1 = Simd4::<u64>::new(4, 5, 6, 7);

        let result = p0.bitxor(p1);

        // You can add assertions here to verify the result if needed
    }
}