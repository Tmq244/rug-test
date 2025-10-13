use core::num::Wrapping;
use core::ops::Neg;

use float::FloatCore;
use Num;

/// Useful functions for signed numbers (i.e. numbers that can be negative).
pub trait Signed: Sized + Num + Neg<Output = Self> {
    /// Computes the absolute value.
    ///
    /// For `f32` and `f64`, `NaN` will be returned if the number is `NaN`.
    ///
    /// For signed integers, `::MIN` will be returned if the number is `::MIN`.
    fn abs(&self) -> Self;

    /// The positive difference of two numbers.
    ///
    /// Returns `zero` if the number is less than or equal to `other`, otherwise the difference
    /// between `self` and `other` is returned.
    fn abs_sub(&self, other: &Self) -> Self;

    /// Returns the sign of the number.
    ///
    /// For `f32` and `f64`:
    ///
    /// * `1.0` if the number is positive, `+0.0` or `INFINITY`
    /// * `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
    /// * `NaN` if the number is `NaN`
    ///
    /// For signed integers:
    ///
    /// * `0` if the number is zero
    /// * `1` if the number is positive
    /// * `-1` if the number is negative
    fn signum(&self) -> Self;

    /// Returns true if the number is positive and false if the number is zero or negative.
    fn is_positive(&self) -> bool;

    /// Returns true if the number is negative and false if the number is zero or positive.
    fn is_negative(&self) -> bool;
}

macro_rules! signed_impl {
    ($($t:ty)*) => ($(
        impl Signed for $t {
            #[inline]
            fn abs(&self) -> $t {
                if self.is_negative() { -*self } else { *self }
            }

            #[inline]
            fn abs_sub(&self, other: &$t) -> $t {
                if *self <= *other { 0 } else { *self - *other }
            }

            #[inline]
            fn signum(&self) -> $t {
                match *self {
                    n if n > 0 => 1,
                    0 => 0,
                    _ => -1,
                }
            }

            #[inline]
            fn is_positive(&self) -> bool { *self > 0 }

            #[inline]
            fn is_negative(&self) -> bool { *self < 0 }
        }
    )*)
}

signed_impl!(isize i8 i16 i32 i64);

#[cfg(has_i128)]
signed_impl!(i128);

impl<T: Signed> Signed for Wrapping<T>
where
    Wrapping<T>: Num + Neg<Output = Wrapping<T>>,
{
    #[inline]
    fn abs(&self) -> Self {
        Wrapping(self.0.abs())
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        Wrapping(self.0.abs_sub(&other.0))
    }

    #[inline]
    fn signum(&self) -> Self {
        Wrapping(self.0.signum())
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.0.is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.0.is_negative()
    }
}

macro_rules! signed_float_impl {
    ($t:ty) => {
        impl Signed for $t {
            /// Computes the absolute value. Returns `NAN` if the number is `NAN`.
            #[inline]
            fn abs(&self) -> $t {
                FloatCore::abs(*self)
            }

            /// The positive difference of two numbers. Returns `0.0` if the number is
            /// less than or equal to `other`, otherwise the difference between`self`
            /// and `other` is returned.
            #[inline]
            fn abs_sub(&self, other: &$t) -> $t {
                if *self <= *other {
                    0.
                } else {
                    *self - *other
                }
            }

            /// # Returns
            ///
            /// - `1.0` if the number is positive, `+0.0` or `INFINITY`
            /// - `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
            /// - `NAN` if the number is NaN
            #[inline]
            fn signum(&self) -> $t {
                FloatCore::signum(*self)
            }

            /// Returns `true` if the number is positive, including `+0.0` and `INFINITY`
            #[inline]
            fn is_positive(&self) -> bool {
                FloatCore::is_sign_positive(*self)
            }

            /// Returns `true` if the number is negative, including `-0.0` and `NEG_INFINITY`
            #[inline]
            fn is_negative(&self) -> bool {
                FloatCore::is_sign_negative(*self)
            }
        }
    };
}

signed_float_impl!(f32);
signed_float_impl!(f64);

/// Computes the absolute value.
///
/// For `f32` and `f64`, `NaN` will be returned if the number is `NaN`
///
/// For signed integers, `::MIN` will be returned if the number is `::MIN`.
#[inline(always)]
pub fn abs<T: Signed>(value: T) -> T {
    value.abs()
}

/// The positive difference of two numbers.
///
/// Returns zero if `x` is less than or equal to `y`, otherwise the difference
/// between `x` and `y` is returned.
#[inline(always)]
pub fn abs_sub<T: Signed>(x: T, y: T) -> T {
    x.abs_sub(&y)
}

/// Returns the sign of the number.
///
/// For `f32` and `f64`:
///
/// * `1.0` if the number is positive, `+0.0` or `INFINITY`
/// * `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
/// * `NaN` if the number is `NaN`
///
/// For signed integers:
///
/// * `0` if the number is zero
/// * `1` if the number is positive
/// * `-1` if the number is negative
#[inline(always)]
pub fn signum<T: Signed>(value: T) -> T {
    value.signum()
}

/// A trait for values which cannot be negative
pub trait Unsigned: Num {}

macro_rules! empty_trait_impl {
    ($name:ident for $($t:ty)*) => ($(
        impl $name for $t {}
    )*)
}

empty_trait_impl!(Unsigned for usize u8 u16 u32 u64);
#[cfg(has_i128)]
empty_trait_impl!(Unsigned for u128);

impl<T: Unsigned> Unsigned for Wrapping<T> where Wrapping<T>: Num {}

#[test]
fn unsigned_wrapping_is_unsigned() {
    fn require_unsigned<T: Unsigned>(_: &T) {}
    require_unsigned(&Wrapping(42_u32));
}

// Commenting this out since it doesn't compile on Rust 1.8,
// because on this version Wrapping doesn't implement Neg and therefore can't
// implement Signed.
// #[test]
// fn signed_wrapping_is_signed() {
//     fn require_signed<T: Signed>(_: &T) {}
//     require_signed(&Wrapping(-42));
// }
#[cfg(test)]
mod tests_rug_1358 {
    use super::*;
    use crate::Signed; // Ensure we have the Signed trait in scope
    use std::f64; // For NaN and other f64 constants

    #[test]
    fn test_abs_i32() {
        let mut p0: i32 = -10;
        assert_eq!(crate::sign::abs(p0), 10);
    }

    #[test]
    fn test_abs_f64_positive() {
        let mut p0: f64 = 10.5;
        assert_eq!(crate::sign::abs(p0), 10.5);
    }

    #[test]
    fn test_abs_f64_negative() {
        let mut p0: f64 = -10.5;
        assert_eq!(crate::sign::abs(p0), 10.5);
    }

    #[test]
    fn test_abs_f64_nan() {
        let mut p0: f64 = f64::NAN;
        assert!(crate::sign::abs(p0).is_nan());
    }

    #[test]
    fn test_abs_i32_min() {
        let mut p0: i32 = i32::MIN;
        assert_eq!(crate::sign::abs(p0), i32::MIN);
    }
}#[cfg(test)]
mod tests_rug_1359 {
    use super::*;
    use crate::{Signed, abs_sub};

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10; // Example concrete implementation of T that satisfies Signed and Sized
        let mut p1: i32 = 4;  // Example concrete implementation of T that satisfies Signed and Sized

        let result = abs_sub(p0, p1);
        assert_eq!(result, 6);

        let p0: i32 = -5;
        let p1: i32 = 3;

        let result = abs_sub(p0, p1);
        assert_eq!(result, 0);

        let p0: i32 = 7;
        let p1: i32 = 7;

        let result = abs_sub(p0, p1);
        assert_eq!(result, 0);

        let p0: i32 = -8;
        let p1: i32 = -10;

        let result = abs_sub(p0, p1);
        assert_eq!(result, 2);
    }
}#[cfg(test)]
mod tests_rug_1360 {
    use super::*;
    use crate::{Signed, sign};
    use std::f32;
    use std::f64;

    #[test]
    fn test_signum_f32() {
        let p0: f32 = 1.0;
        assert_eq!(sign::signum(p0), 1.0);

        let p0: f32 = -1.0;
        assert_eq!(sign::signum(p0), -1.0);

        let p0: f32 = 0.0;
        assert_eq!(sign::signum(p0), 0.0);

        let p0: f32 = -0.0;
        assert_eq!(sign::signum(p0), -0.0);

        let p0: f32 = f32::INFINITY;
        assert_eq!(sign::signum(p0), 1.0);

        let p0: f32 = f32::NEG_INFINITY;
        assert_eq!(sign::signum(p0), -1.0);

        let p0: f32 = f32::NAN;
        assert!(sign::signum(p0).is_nan());
    }

    #[test]
    fn test_signum_f64() {
        let p0: f64 = 1.0;
        assert_eq!(sign::signum(p0), 1.0);

        let p0: f64 = -1.0;
        assert_eq!(sign::signum(p0), -1.0);

        let p0: f64 = 0.0;
        assert_eq!(sign::signum(p0), 0.0);

        let p0: f64 = -0.0;
        assert_eq!(sign::signum(p0), -0.0);

        let p0: f64 = f64::INFINITY;
        assert_eq!(sign::signum(p0), 1.0);

        let p0: f64 = f64::NEG_INFINITY;
        assert_eq!(sign::signum(p0), -1.0);

        let p0: f64 = f64::NAN;
        assert!(sign::signum(p0).is_nan());
    }

    #[test]
    fn test_signum_i32() {
        let p0: i32 = 1;
        assert_eq!(sign::signum(p0), 1);

        let p0: i32 = -1;
        assert_eq!(sign::signum(p0), -1);

        let p0: i32 = 0;
        assert_eq!(sign::signum(p0), 0);
    }

    #[test]
    fn test_signum_i64() {
        let p0: i64 = 1;
        assert_eq!(sign::signum(p0), 1);

        let p0: i64 = -1;
        assert_eq!(sign::signum(p0), -1);

        let p0: i64 = 0;
        assert_eq!(sign::signum(p0), 0);
    }
}#[cfg(test)]
mod tests_rug_1361 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: isize = -42;

        assert_eq!(<isize as Signed>::abs(&p0), 42);
    }
}#[cfg(test)]
mod tests_rug_1362 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: isize = 10;
        let mut p1: isize = 5;

        <isize as Signed>::abs_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1363 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        assert_eq!(<isize as Signed>::signum(&p0), 1);

        p0 = 0;
        assert_eq!(<isize as Signed>::signum(&p0), 0);

        p0 = -35;
        assert_eq!(<isize as Signed>::signum(&p0), -1);
    }
}#[cfg(test)]
mod tests_rug_1364 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42; // Sample data to initialize the variable

        assert_eq!(<isize as Signed>::is_positive(&p0), true);
        
        p0 = -42;
        assert_eq!(<isize as Signed>::is_positive(&p0), false);
        
        p0 = 0;
        assert_eq!(<isize as Signed>::is_positive(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_1365 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: isize = -42;

        assert_eq!(<isize as Signed>::is_negative(&p0), true);

        let p1: isize = 0;
        assert_eq!(<isize as Signed>::is_negative(&p1), false);

        let p2: isize = 42;
        assert_eq!(<isize as Signed>::is_negative(&p2), false);
    }
}#[cfg(test)]
mod tests_rug_1366 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -5;

        assert_eq!(<i8 as Signed>::abs(&p0), 5);
    }
}#[cfg(test)]
mod tests_rug_1367 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 5;

        assert_eq!(<i8 as Signed>::abs_sub(&p0, &p1), 5);
        assert_eq!(<i8 as Signed>::abs_sub(&p1, &p0), 0);
        assert_eq!(<i8 as Signed>::abs_sub(&p1, &p1), 0);
    }
}#[cfg(test)]
mod tests_rug_1368 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for i8

        assert_eq!(<i8 as Signed>::signum(&p0), 1);
        
        p0 = -7;
        assert_eq!(<i8 as Signed>::signum(&p0), -1);
        
        p0 = 0;
        assert_eq!(<i8 as Signed>::signum(&p0), 0);
    }
}#[cfg(test)]
mod tests_rug_1369 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;

        assert!(<i8 as Signed>::is_positive(&p0));

        p0 = -5;
        assert!(!<i8 as Signed>::is_positive(&p0));

        p0 = 0;
        assert!(!<i8 as Signed>::is_positive(&p0));
    }
}#[cfg(test)]
mod tests_rug_1370 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -1;

        assert_eq!(<i8 as Signed>::is_negative(&p0), true);

        let p1: i8 = 0;
        assert_eq!(<i8 as Signed>::is_negative(&p1), false);

        let p2: i8 = 1;
        assert_eq!(<i8 as Signed>::is_negative(&p2), false);
    }
}#[cfg(test)]
mod tests_rug_1371 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i16 = -42;

        assert_eq!(p0.abs(), 42);
    }
}#[cfg(test)]
mod tests_rug_1372 {
    use super::*;
    use crate::sign::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 5;
        let mut p1: i16 = 3;

        assert_eq!(<i16 as Signed>::abs_sub(&p0, &p1), 2);
        
        let mut p0: i16 = -5;
        let mut p1: i16 = 3;

        assert_eq!(<i16 as Signed>::abs_sub(&p0, &p1), 0);
        
        let mut p0: i16 = 3;
        let mut p1: i16 = 5;

        assert_eq!(<i16 as Signed>::abs_sub(&p0, &p1), 0);
    }
}#[cfg(test)]
mod tests_rug_1373 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        assert_eq!(<i16 as Signed>::signum(&p0), 1);

        p0 = -7;
        assert_eq!(<i16 as Signed>::signum(&p0), -1);

        p0 = 0;
        assert_eq!(<i16 as Signed>::signum(&p0), 0);
    }
}#[cfg(test)]
mod tests_rug_1374 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42; // Sample data for i16

        assert_eq!(<i16 as Signed>::is_positive(&p0), true);

        p0 = -1;
        assert_eq!(<i16 as Signed>::is_positive(&p0), false);

        p0 = 0;
        assert_eq!(<i16 as Signed>::is_positive(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_1375 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i16 = -42; // Sample negative i16 value

        assert!(<i16 as Signed>::is_negative(&p0));

        p0 = 0;
        assert!(!<i16 as Signed>::is_negative(&p0));

        p0 = 42;
        assert!(!<i16 as Signed>::is_negative(&p0));
    }
}#[cfg(test)]
mod tests_rug_1376 {
    use super::*;
    use crate::sign::Signed;

    #[test]
    fn test_abs() {
        let mut p0: i32 = -42;

        assert_eq!(<i32 as Signed>::abs(&p0), 42);
        assert_eq!(<i32 as Signed>::abs(&0), 0);
        assert_eq!(<i32 as Signed>::abs(&42), 42);
    }
}#[cfg(test)]
mod tests_rug_1377 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 5;

        assert_eq!(<i32 as Signed>::abs_sub(&p0, &p1), 5);
        
        let mut p0: i32 = -10;
        let mut p1: i32 = 5;

        assert_eq!(<i32 as Signed>::abs_sub(&p0, &p1), 0);

        let mut p0: i32 = 5;
        let mut p1: i32 = 10;

        assert_eq!(<i32 as Signed>::abs_sub(&p0, &p1), 0);

        let mut p0: i32 = 5;
        let mut p1: i32 = -10;

        assert_eq!(<i32 as Signed>::abs_sub(&p0, &p1), 15);
    }
}#[cfg(test)]
mod tests_rug_1378 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i32 = -42;

        assert_eq!(<i32 as Signed>::signum(&p0), -1);
        
        p0 = 0;
        assert_eq!(<i32 as Signed>::signum(&p0), 0);
        
        p0 = 42;
        assert_eq!(<i32 as Signed>::signum(&p0), 1);
    }
}#[cfg(test)]
mod tests_rug_1379 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        assert!(<i32 as Signed>::is_positive(&p0));
        
        p0 = -1;
        assert!(!<i32 as Signed>::is_positive(&p0));
        
        p0 = 0;
        assert!(!<i32 as Signed>::is_positive(&p0));
    }
}#[cfg(test)]
mod tests_rug_1380 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i32 = -42;

        assert!((<i32 as Signed>::is_negative(&p0)));
        
        let p1: i32 = 42;
        assert!(!(<i32 as Signed>::is_negative(&p1)));

        let p2: i32 = 0;
        assert!(!(<i32 as Signed>::is_negative(&p2)));
    }
}#[cfg(test)]
mod tests_rug_1381 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i64 = -12345;

        assert_eq!(<i64 as Signed>::abs(&p0), 12345);
        assert_eq!(<i64 as Signed>::abs(&0), 0);
        assert_eq!(<i64 as Signed>::abs(&12345), 12345);
    }
}#[cfg(test)]
mod tests_rug_1382 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: i64 = 5;

        <i64 as Signed>::abs_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1383 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_signum() {
        let mut p0: i64 = 42; // Example positive value

        assert_eq!(<i64 as Signed>::signum(&p0), 1);

        p0 = 0; // Zero value
        assert_eq!(<i64 as Signed>::signum(&p0), 0);

        p0 = -7; // Example negative value
        assert_eq!(<i64 as Signed>::signum(&p0), -1);
    }
}#[cfg(test)]
mod tests_rug_1384 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123;

        assert_eq!(<i64 as Signed>::is_positive(&p0), true);

        p0 = -456;
        assert_eq!(<i64 as Signed>::is_positive(&p0), false);

        p0 = 0;
        assert_eq!(<i64 as Signed>::is_positive(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_1385 {
    use super::*;
    use crate::sign::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i64 = -42;

        assert_eq!(<i64 as Signed>::is_negative(&p0), true);
        
        let p1: i64 = 0;
        assert_eq!(<i64 as Signed>::is_negative(&p1), false);
        
        let p2: i64 = 42;
        assert_eq!(<i64 as Signed>::is_negative(&p2), false);
    }
}#[cfg(test)]
mod tests_rug_1386 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i128 = -42;

        assert_eq!(<i128 as Signed>::abs(&p0), 42);
    }
}#[cfg(test)]
mod tests_rug_1387 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: i128 = 27;

        assert_eq!(<i128 as Signed>::abs_sub(&p0, &p1), 15);
        assert_eq!(<i128 as Signed>::abs_sub(&p1, &p0), 0);
    }
}#[cfg(test)]
mod tests_rug_1388 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_signum() {
        let p0: i128 = 42; // Sample positive value
        let p1: i128 = 0;  // Zero value
        let p2: i128 = -7; // Sample negative value

        assert_eq!(<i128 as Signed>::signum(&p0), 1);
        assert_eq!(<i128 as Signed>::signum(&p1), 0);
        assert_eq!(<i128 as Signed>::signum(&p2), -1);
    }
}#[cfg(test)]
mod tests_rug_1389 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let p0: i128 = 42;

        assert!((<i128 as Signed>::is_positive)(&p0));
    }

    #[test]
    fn test_zero() {
        let p0: i128 = 0;

        assert!(!(<i128 as Signed>::is_positive)(&p0));
    }

    #[test]
    fn test_negative() {
        let p0: i128 = -42;

        assert!(!(<i128 as Signed>::is_positive)(&p0));
    }
}#[cfg(test)]
mod tests_rug_1390 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: i128 = -42;

        assert_eq!(<i128 as Signed>::is_negative(&p0), true);
        
        p0 = 42;
        assert_eq!(<i128 as Signed>::is_negative(&p0), false);

        p0 = 0;
        assert_eq!(<i128 as Signed>::is_negative(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_1391 {
    use super::*;
    use crate::Signed;
    use core::num::Wrapping;
    use crate::{Num, Zero};

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(-42);

        let result = <core::num::Wrapping<i32> as Signed>::abs(&p0);
        assert_eq!(result, Wrapping(42));
    }
}#[cfg(test)]
mod tests_rug_1392 {
    use super::*;
    use crate::Signed;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(-5);
        let mut p1: Wrapping<i32> = Wrapping(3);

        let result = <Wrapping<i32> as Signed>::abs_sub(&p0, &p1);

        assert_eq!(result, Wrapping(2));
    }
}#[cfg(test)]
mod tests_rug_1393 {
    use super::*;
    use crate::Signed;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        assert_eq!(<Wrapping<i32> as Signed>::signum(&p0), Wrapping(1));
        
        let p1: Wrapping<i32> = Wrapping(-42);
        assert_eq!(<Wrapping<i32> as Signed>::signum(&p1), Wrapping(-1));
        
        let p2: Wrapping<i32> = Wrapping(0);
        assert_eq!(<Wrapping<i32> as Signed>::signum(&p2), Wrapping(0));
    }
}#[cfg(test)]
mod tests_rug_1394 {
    use super::*;
    use crate::Signed;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        assert_eq!(<Wrapping<i32> as Signed>::is_positive(&p0), true);
        
        let p1: Wrapping<i32> = Wrapping(-42);
        assert_eq!(<Wrapping<i32> as Signed>::is_positive(&p1), false);
        
        let p2: Wrapping<i32> = Wrapping(0);
        assert_eq!(<Wrapping<i32> as Signed>::is_positive(&p2), false);
    }
}#[cfg(test)]
mod tests_rug_1395 {
    use super::*;
    use crate::Signed;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(-1);

        assert_eq!(<Wrapping<i32> as Signed>::is_negative(&p0), true);
    }

    #[test]
    fn test_rug_positive() {
        let mut p0: Wrapping<i32> = Wrapping(1);

        assert_eq!(<Wrapping<i32> as Signed>::is_negative(&p0), false);
    }

    #[test]
    fn test_rug_zero() {
        let mut p0: Wrapping<i32> = Wrapping(0);

        assert_eq!(<Wrapping<i32> as Signed>::is_negative(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_1396 {
    use super::*;
    use crate::sign::Signed;
    
    #[test]
    fn test_abs() {
        let mut p0: f32 = -3.14;

        assert_eq!(p0.abs(), 3.14);
    }
}#[cfg(test)]
mod tests_rug_1397 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 5.0;
        let mut p1: f32 = 3.0;

        <f32 as Signed>::abs_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1398 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        assert_eq!(p0.signum(), 1.0);

        p0 = -123.456;
        assert_eq!(p0.signum(), -1.0);

        p0 = 0.0;
        assert_eq!(p0.signum(), 0.0);

        p0 = -0.0;
        assert_eq!(p0.signum(), -0.0);

        p0 = f32::INFINITY;
        assert_eq!(p0.signum(), 1.0);

        p0 = f32::NEG_INFINITY;
        assert_eq!(p0.signum(), -1.0);

        p0 = f32::NAN;
        assert!(p0.signum().is_nan());
    }
}#[cfg(test)]
mod tests_rug_1399 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let p0: f32 = 42.0;

        assert_eq!(<f32 as Signed>::is_positive(&p0), true);
    }

    #[test]
    fn test_zero() {
        let p0: f32 = 0.0;

        assert_eq!(<f32 as Signed>::is_positive(&p0), true);
    }

    #[test]
    fn test_negative() {
        let p0: f32 = -1.0;

        assert_eq!(<f32 as Signed>::is_positive(&p0), false);
    }

    #[test]
    fn test_infinity() {
        let p0: f32 = std::f32::INFINITY;

        assert_eq!(<f32 as Signed>::is_positive(&p0), true);
    }

    #[test]
    fn test_nan() {
        let p0: f32 = std::f32::NAN;

        assert_eq!(<f32 as Signed>::is_positive(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_1400 {
    use super::*;
    use crate::sign::Signed;

    #[test]
    fn test_rug() {
        let mut p0: f32 = -1.0; // Sample data for f32

        assert_eq!(p0.is_negative(), true);
        
        let p1: f32 = 0.0;
        assert_eq!(p1.is_negative(), false);
        
        let p2: f32 = -0.0;
        assert_eq!(p2.is_negative(), true);
        
        let p3: f32 = 1.0;
        assert_eq!(p3.is_negative(), false);
        
        let p4: f32 = std::f32::NEG_INFINITY;
        assert_eq!(p4.is_negative(), true);
        
        let p5: f32 = std::f32::INFINITY;
        assert_eq!(p5.is_negative(), false);
    }
}#[cfg(test)]
mod tests_rug_1401 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: f64 = -3.14;

        assert_eq!(p0.abs(), 3.14);
    }
}#[cfg(test)]
mod tests_rug_1402 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 5.0;
        let mut p1: f64 = 3.0;

        assert_eq!(<f64 as Signed>::abs_sub(&p0, &p1), 2.0);
        assert_eq!(<f64 as Signed>::abs_sub(&p1, &p0), 0.0);
    }
}#[cfg(test)]
mod tests_rug_1403 {
    use super::*;
    use crate::Signed;
    #[test]
    fn test_signum() {
        let p0: f64 = 42.0;

        assert_eq!(p0.signum(), 1.0);

        let p1: f64 = -42.0;
        assert_eq!(p1.signum(), -1.0);

        let p2: f64 = 0.0;
        assert_eq!(p2.signum(), 1.0);

        let p3: f64 = -0.0;
        assert_eq!(p3.signum(), -1.0);

        let p4: f64 = f64::INFINITY;
        assert_eq!(p4.signum(), 1.0);

        let p5: f64 = f64::NEG_INFINITY;
        assert_eq!(p5.signum(), -1.0);

        let p6: f64 = f64::NAN;
        assert!(p6.signum().is_nan());
    }
}#[cfg(test)]
mod tests_rug_1404 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.45;

        assert!(<f64 as Signed>::is_positive(&p0));

        p0 = -123.45;
        assert!(!<f64 as Signed>::is_positive(&p0));

        p0 = 0.0;
        assert!(<f64 as Signed>::is_positive(&p0));

        p0 = -0.0;
        assert!(!<f64 as Signed>::is_positive(&p0));

        p0 = f64::INFINITY;
        assert!(<f64 as Signed>::is_positive(&p0));

        p0 = f64::NEG_INFINITY;
        assert!(!<f64 as Signed>::is_positive(&p0));
    }
}#[cfg(test)]
mod tests_rug_1405 {
    use super::*;
    use crate::Signed;

    #[test]
    fn test_rug() {
        let mut p0: f64 = -3.14;

        assert!(p0.is_negative());

        let p1: f64 = 0.0;
        assert!(!p1.is_negative());

        let p2: f64 = -0.0;
        assert!(p2.is_negative());

        let p3: f64 = 2.71;
        assert!(!p3.is_negative());

        let p4: f64 = f64::NEG_INFINITY;
        assert!(p4.is_negative());

        let p5: f64 = f64::INFINITY;
        assert!(!p5.is_negative());
    }
}