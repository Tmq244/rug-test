use core::num::Wrapping;
use core::{f32, f64};
#[cfg(has_i128)]
use core::{i128, u128};
use core::{i16, i32, i64, i8, isize};
use core::{u16, u32, u64, u8, usize};

/// Numbers which have upper and lower bounds
pub trait Bounded {
    // FIXME (#5527): These should be associated constants
    /// Returns the smallest finite number this type can represent
    fn min_value() -> Self;
    /// Returns the largest finite number this type can represent
    fn max_value() -> Self;
}

/// Numbers which have lower bounds
pub trait LowerBounded {
    /// Returns the smallest finite number this type can represent
    fn min_value() -> Self;
}

// FIXME: With a major version bump, this should be a supertrait instead
impl<T: Bounded> LowerBounded for T {
    fn min_value() -> T {
        Bounded::min_value()
    }
}

/// Numbers which have upper bounds
pub trait UpperBounded {
    /// Returns the largest finite number this type can represent
    fn max_value() -> Self;
}

// FIXME: With a major version bump, this should be a supertrait instead
impl<T: Bounded> UpperBounded for T {
    fn max_value() -> T {
        Bounded::max_value()
    }
}

macro_rules! bounded_impl {
    ($t:ty, $min:expr, $max:expr) => {
        impl Bounded for $t {
            #[inline]
            fn min_value() -> $t {
                $min
            }

            #[inline]
            fn max_value() -> $t {
                $max
            }
        }
    };
}

bounded_impl!(usize, usize::MIN, usize::MAX);
bounded_impl!(u8, u8::MIN, u8::MAX);
bounded_impl!(u16, u16::MIN, u16::MAX);
bounded_impl!(u32, u32::MIN, u32::MAX);
bounded_impl!(u64, u64::MIN, u64::MAX);
#[cfg(has_i128)]
bounded_impl!(u128, u128::MIN, u128::MAX);

bounded_impl!(isize, isize::MIN, isize::MAX);
bounded_impl!(i8, i8::MIN, i8::MAX);
bounded_impl!(i16, i16::MIN, i16::MAX);
bounded_impl!(i32, i32::MIN, i32::MAX);
bounded_impl!(i64, i64::MIN, i64::MAX);
#[cfg(has_i128)]
bounded_impl!(i128, i128::MIN, i128::MAX);

impl<T: Bounded> Bounded for Wrapping<T> {
    fn min_value() -> Self {
        Wrapping(T::min_value())
    }
    fn max_value() -> Self {
        Wrapping(T::max_value())
    }
}

bounded_impl!(f32, f32::MIN, f32::MAX);

macro_rules! for_each_tuple_ {
    ( $m:ident !! ) => (
        $m! { }
    );
    ( $m:ident !! $h:ident, $($t:ident,)* ) => (
        $m! { $h $($t)* }
        for_each_tuple_! { $m !! $($t,)* }
    );
}
macro_rules! for_each_tuple {
    ($m:ident) => {
        for_each_tuple_! { $m !! A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, }
    };
}

macro_rules! bounded_tuple {
    ( $($name:ident)* ) => (
        impl<$($name: Bounded,)*> Bounded for ($($name,)*) {
            #[inline]
            fn min_value() -> Self {
                ($($name::min_value(),)*)
            }
            #[inline]
            fn max_value() -> Self {
                ($($name::max_value(),)*)
            }
        }
    );
}

for_each_tuple!(bounded_tuple);
bounded_impl!(f64, f64::MIN, f64::MAX);

#[test]
fn wrapping_bounded() {
    macro_rules! test_wrapping_bounded {
        ($($t:ty)+) => {
            $(
                assert_eq!(<Wrapping<$t> as Bounded>::min_value().0, <$t>::min_value());
                assert_eq!(<Wrapping<$t> as Bounded>::max_value().0, <$t>::max_value());
            )+
        };
    }

    test_wrapping_bounded!(usize u8 u16 u32 u64 isize i8 i16 i32 i64);
}

#[cfg(has_i128)]
#[test]
fn wrapping_bounded_i128() {
    macro_rules! test_wrapping_bounded {
        ($($t:ty)+) => {
            $(
                assert_eq!(<Wrapping<$t> as Bounded>::min_value().0, <$t>::min_value());
                assert_eq!(<Wrapping<$t> as Bounded>::max_value().0, <$t>::max_value());
            )+
        };
    }

    test_wrapping_bounded!(u128 i128);
}

#[test]
fn wrapping_is_bounded() {
    fn require_bounded<T: Bounded>(_: &T) {}
    require_bounded(&Wrapping(42_u32));
    require_bounded(&Wrapping(-42));
}
#[cfg(test)]
mod tests_rug_1429 {
    use super::*;
    use crate::bounds::LowerBounded;
    use crate::Bounded;

    #[test]
    fn test_min_value_i32() {
        let min_i32: i32 = <i32 as LowerBounded>::min_value();
        assert_eq!(min_i32, i32::MIN);
    }

    #[test]
    fn test_min_value_u32() {
        let min_u32: u32 = <u32 as LowerBounded>::min_value();
        assert_eq!(min_u32, u32::MIN);
    }

    #[test]
    fn test_min_value_f64() {
        let min_f64: f64 = <f64 as LowerBounded>::min_value();
        assert_eq!(min_f64, f64::MIN);
    }
}#[cfg(test)]
mod tests_rug_1430 {
    use super::*;
    use crate::bounds::UpperBounded;
    use crate::Bounded;

    #[test]
    fn test_max_value_i32() {
        let max_i32: i32 = <i32 as UpperBounded>::max_value();
        assert_eq!(max_i32, i32::MAX);
    }

    #[test]
    fn test_max_value_u64() {
        let max_u64: u64 = <u64 as UpperBounded>::max_value();
        assert_eq!(max_u64, u64::MAX);
    }

    #[test]
    fn test_max_value_f32() {
        let max_f32: f32 = <f32 as UpperBounded>::max_value();
        assert_eq!(max_f32, f32::MAX);
    }
}#[cfg(test)]
mod tests_rug_1431 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_usize: usize = <usize as Bounded>::min_value();
        assert_eq!(min_usize, 0);
    }
}#[cfg(test)]
mod tests_rug_1432 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value() {
        let max_usize: usize = <usize as Bounded>::max_value();
        assert_eq!(max_usize, std::usize::MAX);
    }
}#[cfg(test)]
mod tests_rug_1433 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_u8: u8 = <u8 as Bounded>::min_value();
        assert_eq!(min_u8, 0);
    }
}#[cfg(test)]
mod tests_rug_1434 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let max_u8: u8 = <u8 as Bounded>::max_value();

        assert_eq!(max_u8, 255);
    }
}#[cfg(test)]
mod tests_rug_1435 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_min_value() {
        let min_u16: u16 = <u16 as Bounded>::min_value();
        assert_eq!(min_u16, 0);
    }
}#[cfg(test)]
mod tests_rug_1436 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value() {
        let max_u16: u16 = <u16 as Bounded>::max_value();
        
        assert_eq!(max_u16, 65535);
    }
}#[cfg(test)]
mod tests_rug_1437 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let min_u32: u32 = <u32 as Bounded>::min_value();
        
        assert_eq!(min_u32, 0);
    }
}#[cfg(test)]
mod tests_rug_1438 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value_u32() {
        let max_u32: u32 = <u32 as Bounded>::max_value();
        assert_eq!(max_u32, 4294967295);
    }
}#[cfg(test)]
mod tests_rug_1439 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_u64: u64 = <u64 as Bounded>::min_value();
        
        assert_eq!(min_u64, 0);
    }
}#[cfg(test)]
mod tests_rug_1440 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let max_u64: u64 = <u64 as Bounded>::max_value();
        
        assert_eq!(max_u64, 18446744073709551615);
    }
}#[cfg(test)]
mod tests_rug_1441 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_u128: u128 = <u128 as Bounded>::min_value();
        
        assert_eq!(min_u128, 0);
    }
}#[cfg(test)]
mod tests_rug_1442 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let max_u128: u128 = <u128 as Bounded>::max_value();

        assert_eq!(max_u128, u128::MAX);
    }
}#[cfg(test)]
mod tests_rug_1443 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value_isize() {
        let min_val: isize = <isize as Bounded>::min_value();
        assert_eq!(min_val, std::isize::MIN);
    }
}#[cfg(test)]
mod tests_rug_1444 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value_isize() {
        let max_isize: isize = <isize as Bounded>::max_value();
        
        assert_eq!(max_isize, isize::MAX);
    }
}#[cfg(test)]
mod tests_rug_1445 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_i8: i8 = <i8 as Bounded>::min_value();
        
        assert_eq!(min_i8, -128);
    }
}#[cfg(test)]
mod tests_rug_1446 {
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value_i8() {
        let max_val: i8 = <i8 as Bounded>::max_value();
        assert_eq!(max_val, 127);
    }
}#[cfg(test)]
mod tests_rug_1447 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_min_value() {
        let min_i16: i16 = <i16 as Bounded>::min_value();
        
        assert_eq!(min_i16, -32768);
    }
}#[cfg(test)]
mod tests_rug_1448 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value() {
        let max_i16: i16 = <i16 as Bounded>::max_value();
        assert_eq!(max_i16, 32767);
    }
}#[cfg(test)]
mod tests_rug_1449 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_i32: i32 = <i32 as Bounded>::min_value();
        assert_eq!(min_i32, i32::MIN);
    }
}#[cfg(test)]
mod tests_rug_1450 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let max_i32: i32 = <i32 as Bounded>::max_value();
        
        assert_eq!(max_i32, 2147483647);
    }
}#[cfg(test)]
mod tests_rug_1451 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_min_value() {
        let min_i64: i64 = <i64 as Bounded>::min_value();
        
        assert_eq!(min_i64, -9223372036854775808);
    }
}#[cfg(test)]
mod tests_rug_1452 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let max_i64: i64 = <i64 as Bounded>::max_value();

        assert_eq!(max_i64, 9223372036854775807);
    }
}#[cfg(test)]
mod tests_rug_1453 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_i128: i128 = <i128 as Bounded>::min_value();
        
        assert_eq!(min_i128, -170141183460469231731687303715884105728);
    }
}#[cfg(test)]
mod tests_rug_1454 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_max_value() {
        let max_i128: i128 = <i128 as Bounded>::max_value();
        
        assert_eq!(max_i128, i128::MAX);
    }
}#[cfg(test)]
mod tests_rug_1457 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_min_value() {
        let min_f32: f32 = <f32 as Bounded>::min_value();
        assert_eq!(min_f32, std::f32::MIN);
    }
}#[cfg(test)]
mod tests_rug_1458 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let max_f32: f32 = <f32 as Bounded>::max_value();

        assert_eq!(max_f32, std::f32::MAX);
    }
}#[cfg(test)]
mod tests_rug_1463 {
    use super::*;
    use crate::Bounded;
    
    #[test]
    fn test_rug() {
        // Assuming C through T are of types that implement Bounded, we'll use i32 as a sample type.
        let c: i32 = 0;
        let d: i32 = 0;
        let e: i32 = 0;
        let f: i32 = 0;
        let g: i32 = 0;
        let h: i32 = 0;
        let i: i32 = 0;
        let j: i32 = 0;
        let k: i32 = 0;
        let l: i32 = 0;
        let m: i32 = 0;
        let n: i32 = 0;
        let o: i32 = 0;
        let p: i32 = 0;
        let q: i32 = 0;
        let r: i32 = 0;
        let s: i32 = 0;
        let t: i32 = 0;

        <(i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1472 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let g: i8 = 0;
        let h: u8 = 0;
        let i: i16 = 0;
        let j: u16 = 0;
        let k: i32 = 0;
        let l: u32 = 0;
        let m: i64 = 0;
        let n: u64 = 0;
        let o: i128 = 0;
        let p: u128 = 0;
        let q: f32 = 0.0;
        let r: f64 = 0.0;
        let s: isize = 0;
        let t: usize = 0;

        <(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, f32, f64, isize, usize) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1474 {
    use super::*;
    use crate::Bounded;
    use crate::{Zero, One};

    #[test]
    fn test_rug() {
        let h: i8 = Zero::zero();
        let i: u8 = One::one();
        let j: i16 = Zero::zero();
        let k: u16 = One::one();
        let l: i32 = Zero::zero();
        let m: u32 = One::one();
        let n: i64 = Zero::zero();
        let o: u64 = One::one();
        let p: isize = Zero::zero();
        let q: usize = One::one();
        let r: i128 = Zero::zero();
        let s: u128 = One::one();
        let t: f32 = Zero::zero();

        <(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize, i128, u128, f32) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1475 {
    use super::*;
    use crate::bounds::Bounded;
    
    #[test]
    fn test_rug() {
        let i: i8 = 0;
        let j: u8 = 0;
        let k: i16 = 0;
        let l: u16 = 0;
        let m: i32 = 0;
        let n: u32 = 0;
        let o: i64 = 0;
        let p: u64 = 0;
        let q: i128 = 0;
        let r: u128 = 0;
        let s: isize = 0;
        let t: usize = 0;

        <(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1476 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let i: i8 = 0;
        let j: u8 = 1;
        let k: i16 = 2;
        let l: u16 = 3;
        let m: i32 = 4;
        let n: u32 = 5;
        let o: i64 = 6;
        let p: u64 = 7;
        let q: isize = 8;
        let r: usize = 9;
        let s: f32 = 10.0;
        let t: f64 = 11.0;

        <(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize, f32, f64) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1478 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let j: i32 = 10;
        let k: u64 = 20;
        let l: isize = 30;
        let m: usize = 40;
        let n: i8 = 50;
        let o: u8 = 60;
        let p: i16 = 70;
        let q: u16 = 80;
        let r: i64 = 90;
        let s: u32 = 100;
        let t: f32 = 110.0;

        <(i32, u64, isize, usize, i8, u8, i16, u16, i64, u32, f32) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1479 {
    use super::*;
    use crate::Bounded;
    
    #[test]
    fn test_rug() {
        let k: i8 = 0;
        let l: u16 = 1;
        let m: i32 = -1;
        let n: u32 = 2;
        let o: i64 = -2;
        let p: u64 = 3;
        let q: isize = -3;
        let r: usize = 4;
        let s: f32 = 5.0;
        let t: f64 = 6.0;

        <(i8, u16, i32, u32, i64, u64, isize, usize, f32, f64) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1481 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let a: i8 = 0;
        let b: u8 = 0;
        let c: i16 = 0;
        let d: u16 = 0;
        let e: i32 = 0;
        let f: u32 = 0;
        let g: i64 = 0;
        let h: u64 = 0;
        let i: isize = 0;

        <(i8, u8, i16, u16, i32, u32, i64, u64, isize) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1482 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let l: i8 = 0;
        let m: u16 = 0;
        let n: i32 = 0;
        let o: u32 = 0;
        let p: i64 = 0;
        let q: u64 = 0;
        let r: i128 = 0;
        let s: u128 = 0;
        let t: isize = 0;

        <(i8, u16, i32, u32, i64, u64, i128, u128, isize) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1483 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let m: i32 = 0;
        let n: i32 = 1;
        let o: i32 = 2;
        let p: i32 = 3;
        let q: i32 = 4;
        let r: i32 = 5;
        let s: i32 = 6;
        let t: i32 = 7;

        <(i32, i32, i32, i32, i32, i32, i32, i32) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1484 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let m: i8 = 1;
        let n: u8 = 2;
        let o: i16 = 3;
        let p: u16 = 4;
        let q: i32 = 5;
        let r: u32 = 6;
        let s: i64 = 7;
        let t: u64 = 8;

        <(i8, u8, i16, u16, i32, u32, i64, u64) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1485 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let n: i8 = 1;
        let o: u8 = 2;
        let p: i16 = 3;
        let q: u16 = 4;
        let r: i32 = 5;
        let s: u32 = 6;
        let t: i64 = 7;

        <(i8, u8, i16, u16, i32, u32, i64) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1487 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        // Assuming O, P, Q, R, S, T are types that implement Bounded trait
        // For the sake of this example, let's assume they are i32, i64, u32, u64, f32, f64 respectively

        let result: (i32, i64, u32, u64, f32, f64) = <(i32, i64, u32, u64, f32, f64) as Bounded>::min_value();

        assert_eq!(result.0, i32::min_value());
        assert_eq!(result.1, i64::min_value());
        assert_eq!(result.2, u32::min_value());
        assert_eq!(result.3, u64::min_value());
        assert_eq!(result.4, f32::MIN);
        assert_eq!(result.5, f64::MIN);
    }
}#[cfg(test)]
mod tests_rug_1488 {
    use super::*;
    use crate::bounds::Bounded;
    use crate::{One, Zero};

    #[test]
    fn test_rug() {
        let o: i8 = One::one();
        let p: u8 = Zero::zero();
        let q: i16 = One::one();
        let r: u16 = Zero::zero();
        let s: i32 = One::one();
        let t: u32 = Zero::zero();

        <(i8, u8, i16, u16, i32, u32) as Bounded>::max_value();

        // Example usage of the max_value
        let result = <(i8, u8, i16, u16, i32, u32) as Bounded>::max_value();
        assert_eq!(result, (i8::MAX, u8::MAX, i16::MAX, u16::MAX, i32::MAX, u32::MAX));
    }
}#[cfg(test)]
mod tests_rug_1489 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let p: i32 = 10;
        let q: u32 = 20;
        let r: i64 = 30;
        let s: u64 = 40;
        let t: isize = 50;

        <(i32, u32, i64, u64, isize) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1490 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let p: i8 = 0;
        let q: u16 = 1;
        let r: i32 = -1;
        let s: u32 = 2;
        let t: i64 = 3;

        <(i8, u16, i32, u32, i64) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1491 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let q: i8 = 0;
        let r: u16 = 0;
        let s: i32 = 0;
        let t: u64 = 0;

        <(i8, u16, i32, u64) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1492 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value() {
        let q: i32 = 10;
        let r: u32 = 20;
        let s: i64 = 30;
        let t: u64 = 40;

        let max_values = <(i32, u32, i64, u64) as Bounded>::max_value();

        assert_eq!(max_values, (i32::max_value(), u32::max_value(), i64::max_value(), u64::max_value()));
    }
}#[cfg(test)]
mod tests_rug_1493 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_rug() {
        let r: i32 = 10;
        let s: u64 = 20;
        let t: f64 = 30.0;

        <(i32, u64, f64) as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1494 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value() {
        let r: i8 = 0;
        let s: u16 = 0;
        let t: f32 = 0.0;

        <(i8, u16, f32) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1495 {
    use super::*;
    use crate::Bounded;

    #[test]
    fn test_min_value() {
        let s: i32 = 10;
        let t: u32 = 20;

        let min_value_result: (i32, u32) = <(i32, u32) as Bounded>::min_value();

        assert_eq!(min_value_result, (i32::min_value(), u32::min_value()));
    }
}#[cfg(test)]
mod tests_rug_1496 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let a: i32 = 10;
        let b: u32 = 20;

        <(i32, u32) as Bounded>::max_value();
    }
}#[cfg(test)]
mod tests_rug_1497 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let sample: (i32,) = (42,);
        let min_val: (i32,) = <(i32,) as Bounded>::min_value();

        assert_eq!(min_val, (std::i32::MIN,))
    }
}#[cfg(test)]
mod tests_rug_1498 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_rug() {
        let sample_u32: u32 = 42;
        let sample_i32: i32 = -42;
        let sample_f64: f64 = 3.14;

        let tuple: (u32,) = (sample_u32,);
        assert_eq!(<(u32,) as Bounded>::max_value(), (u32::MAX,));

        let tuple: (i32,) = (sample_i32,);
        assert_eq!(<(i32,) as Bounded>::max_value(), (i32::MAX,));

        let tuple: (f64,) = (sample_f64,);
        assert_eq!(<(f64,) as Bounded>::max_value(), (f64::MAX,));
    }
}#[cfg(test)]
mod tests_rug_1499 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let result: () = <() as Bounded>::min_value();
    }
}#[cfg(test)]
mod tests_rug_1500 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value() {
        let max_unit: () = <() as Bounded>::max_value();
        
        // Since `()` is a unit type, it doesn't have any meaningful values to compare,
        // but this demonstrates how you would call the method.
        assert_eq!(max_unit, ());
    }
}#[cfg(test)]
mod tests_rug_1501 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_min_value() {
        let min_f64: f64 = <f64 as Bounded>::min_value();
        assert_eq!(min_f64, f64::MIN);
    }
}#[cfg(test)]
mod tests_rug_1502 {
    use super::*;
    use crate::bounds::Bounded;

    #[test]
    fn test_max_value() {
        let max_f64: f64 = <f64 as Bounded>::max_value();

        assert_eq!(max_f64, std::f64::MAX);
    }
}