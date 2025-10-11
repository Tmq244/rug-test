use core::num::Wrapping;
use core::ops::Mul;
use {CheckedMul, One};

/// Binary operator for raising a value to a power.
pub trait Pow<RHS> {
    /// The result after applying the operator.
    type Output;

    /// Returns `self` to the power `rhs`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::Pow;
    /// assert_eq!(Pow::pow(10u32, 2u32), 100);
    /// ```
    fn pow(self, rhs: RHS) -> Self::Output;
}

macro_rules! pow_impl {
    ($t:ty) => {
        pow_impl!($t, u8);
        pow_impl!($t, usize);

        // FIXME: these should be possible
        // pow_impl!($t, u16);
        // pow_impl!($t, u32);
        // pow_impl!($t, u64);
    };
    ($t:ty, $rhs:ty) => {
        pow_impl!($t, $rhs, usize, pow);
    };
    ($t:ty, $rhs:ty, $desired_rhs:ty, $method:expr) => {
        impl Pow<$rhs> for $t {
            type Output = $t;
            #[inline]
            fn pow(self, rhs: $rhs) -> $t {
                ($method)(self, <$desired_rhs>::from(rhs))
            }
        }

        impl<'a> Pow<&'a $rhs> for $t {
            type Output = $t;
            #[inline]
            fn pow(self, rhs: &'a $rhs) -> $t {
                ($method)(self, <$desired_rhs>::from(*rhs))
            }
        }

        impl<'a> Pow<$rhs> for &'a $t {
            type Output = $t;
            #[inline]
            fn pow(self, rhs: $rhs) -> $t {
                ($method)(*self, <$desired_rhs>::from(rhs))
            }
        }

        impl<'a, 'b> Pow<&'a $rhs> for &'b $t {
            type Output = $t;
            #[inline]
            fn pow(self, rhs: &'a $rhs) -> $t {
                ($method)(*self, <$desired_rhs>::from(*rhs))
            }
        }
    };
}

pow_impl!(u8, u8, u32, u8::pow);
pow_impl!(u8, u16, u32, u8::pow);
pow_impl!(u8, u32, u32, u8::pow);
pow_impl!(u8, usize);
pow_impl!(i8, u8, u32, i8::pow);
pow_impl!(i8, u16, u32, i8::pow);
pow_impl!(i8, u32, u32, i8::pow);
pow_impl!(i8, usize);
pow_impl!(u16, u8, u32, u16::pow);
pow_impl!(u16, u16, u32, u16::pow);
pow_impl!(u16, u32, u32, u16::pow);
pow_impl!(u16, usize);
pow_impl!(i16, u8, u32, i16::pow);
pow_impl!(i16, u16, u32, i16::pow);
pow_impl!(i16, u32, u32, i16::pow);
pow_impl!(i16, usize);
pow_impl!(u32, u8, u32, u32::pow);
pow_impl!(u32, u16, u32, u32::pow);
pow_impl!(u32, u32, u32, u32::pow);
pow_impl!(u32, usize);
pow_impl!(i32, u8, u32, i32::pow);
pow_impl!(i32, u16, u32, i32::pow);
pow_impl!(i32, u32, u32, i32::pow);
pow_impl!(i32, usize);
pow_impl!(u64, u8, u32, u64::pow);
pow_impl!(u64, u16, u32, u64::pow);
pow_impl!(u64, u32, u32, u64::pow);
pow_impl!(u64, usize);
pow_impl!(i64, u8, u32, i64::pow);
pow_impl!(i64, u16, u32, i64::pow);
pow_impl!(i64, u32, u32, i64::pow);
pow_impl!(i64, usize);

#[cfg(has_i128)]
pow_impl!(u128, u8, u32, u128::pow);
#[cfg(has_i128)]
pow_impl!(u128, u16, u32, u128::pow);
#[cfg(has_i128)]
pow_impl!(u128, u32, u32, u128::pow);
#[cfg(has_i128)]
pow_impl!(u128, usize);

#[cfg(has_i128)]
pow_impl!(i128, u8, u32, i128::pow);
#[cfg(has_i128)]
pow_impl!(i128, u16, u32, i128::pow);
#[cfg(has_i128)]
pow_impl!(i128, u32, u32, i128::pow);
#[cfg(has_i128)]
pow_impl!(i128, usize);

pow_impl!(usize, u8, u32, usize::pow);
pow_impl!(usize, u16, u32, usize::pow);
pow_impl!(usize, u32, u32, usize::pow);
pow_impl!(usize, usize);
pow_impl!(isize, u8, u32, isize::pow);
pow_impl!(isize, u16, u32, isize::pow);
pow_impl!(isize, u32, u32, isize::pow);
pow_impl!(isize, usize);
pow_impl!(Wrapping<u8>);
pow_impl!(Wrapping<i8>);
pow_impl!(Wrapping<u16>);
pow_impl!(Wrapping<i16>);
pow_impl!(Wrapping<u32>);
pow_impl!(Wrapping<i32>);
pow_impl!(Wrapping<u64>);
pow_impl!(Wrapping<i64>);
#[cfg(has_i128)]
pow_impl!(Wrapping<u128>);
#[cfg(has_i128)]
pow_impl!(Wrapping<i128>);
pow_impl!(Wrapping<usize>);
pow_impl!(Wrapping<isize>);

// FIXME: these should be possible
// pow_impl!(u8, u64);
// pow_impl!(i16, u64);
// pow_impl!(i8, u64);
// pow_impl!(u16, u64);
// pow_impl!(u32, u64);
// pow_impl!(i32, u64);
// pow_impl!(u64, u64);
// pow_impl!(i64, u64);
// pow_impl!(usize, u64);
// pow_impl!(isize, u64);

#[cfg(any(feature = "std", feature = "libm"))]
mod float_impls {
    use super::Pow;
    use Float;

    pow_impl!(f32, i8, i32, <f32 as Float>::powi);
    pow_impl!(f32, u8, i32, <f32 as Float>::powi);
    pow_impl!(f32, i16, i32, <f32 as Float>::powi);
    pow_impl!(f32, u16, i32, <f32 as Float>::powi);
    pow_impl!(f32, i32, i32, <f32 as Float>::powi);
    pow_impl!(f64, i8, i32, <f64 as Float>::powi);
    pow_impl!(f64, u8, i32, <f64 as Float>::powi);
    pow_impl!(f64, i16, i32, <f64 as Float>::powi);
    pow_impl!(f64, u16, i32, <f64 as Float>::powi);
    pow_impl!(f64, i32, i32, <f64 as Float>::powi);
    pow_impl!(f32, f32, f32, <f32 as Float>::powf);
    pow_impl!(f64, f32, f64, <f64 as Float>::powf);
    pow_impl!(f64, f64, f64, <f64 as Float>::powf);
}

/// Raises a value to the power of exp, using exponentiation by squaring.
///
/// Note that `0⁰` (`pow(0, 0)`) returns `1`. Mathematically this is undefined.
///
/// # Example
///
/// ```rust
/// use num_traits::pow;
///
/// assert_eq!(pow(2i8, 4), 16);
/// assert_eq!(pow(6u8, 3), 216);
/// assert_eq!(pow(0u8, 0), 1); // Be aware if this case affects you
/// ```
#[inline]
pub fn pow<T: Clone + One + Mul<T, Output = T>>(mut base: T, mut exp: usize) -> T {
    if exp == 0 {
        return T::one();
    }

    while exp & 1 == 0 {
        base = base.clone() * base;
        exp >>= 1;
    }
    if exp == 1 {
        return base;
    }

    let mut acc = base.clone();
    while exp > 1 {
        exp >>= 1;
        base = base.clone() * base;
        if exp & 1 == 1 {
            acc = acc * base.clone();
        }
    }
    acc
}

/// Raises a value to the power of exp, returning `None` if an overflow occurred.
///
/// Note that `0⁰` (`checked_pow(0, 0)`) returns `Some(1)`. Mathematically this is undefined.
///
/// Otherwise same as the `pow` function.
///
/// # Example
///
/// ```rust
/// use num_traits::checked_pow;
///
/// assert_eq!(checked_pow(2i8, 4), Some(16));
/// assert_eq!(checked_pow(7i8, 8), None);
/// assert_eq!(checked_pow(7u32, 8), Some(5_764_801));
/// assert_eq!(checked_pow(0u32, 0), Some(1)); // Be aware if this case affect you
/// ```
#[inline]
pub fn checked_pow<T: Clone + One + CheckedMul>(mut base: T, mut exp: usize) -> Option<T> {
    if exp == 0 {
        return Some(T::one());
    }

    macro_rules! optry {
        ($expr:expr) => {
            if let Some(val) = $expr {
                val
            } else {
                return None;
            }
        };
    }

    while exp & 1 == 0 {
        base = optry!(base.checked_mul(&base));
        exp >>= 1;
    }
    if exp == 1 {
        return Some(base);
    }

    let mut acc = base.clone();
    while exp > 1 {
        exp >>= 1;
        base = optry!(base.checked_mul(&base));
        if exp & 1 == 1 {
            acc = optry!(acc.checked_mul(&base));
        }
    }
    Some(acc)
}
#[cfg(test)]
mod tests_rug_1016 {
    use super::*;
    use crate::{One, Mul};
    use core::marker::Sized;
    use core::clone::Clone;

    #[derive(Debug, Clone, PartialEq)]
    struct MyNumber(u8);

    impl One for MyNumber {
        fn one() -> Self {
            MyNumber(1)
        }
    }

    impl Mul<Self> for MyNumber {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            MyNumber(self.0 * rhs.0)
        }
    }

    #[test]
    fn test_pow() {
        let mut p0: MyNumber = MyNumber(2);
        let mut p1: usize = 4;

        assert_eq!(crate::pow::pow(p0, p1), MyNumber(16));

        p0 = MyNumber(6);
        p1 = 3;
        assert_eq!(crate::pow::pow(p0, p1), MyNumber(216));

        p0 = MyNumber(0);
        p1 = 0;
        assert_eq!(crate::pow::pow(p0, p1), MyNumber(1));
    }
}#[cfg(test)]
mod tests_rug_1017 {
    use super::*;
    use crate::{One, CheckedMul};

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: usize = 4;

        assert_eq!(crate::pow::checked_pow(p0, p1), Some(16));

        let mut p0: i8 = 7;
        let mut p1: usize = 8;

        assert_eq!(crate::pow::checked_pow(p0, p1), None);

        let mut p0: u32 = 7;
        let mut p1: usize = 8;

        assert_eq!(crate::pow::checked_pow(p0, p1), Some(5_764_801));

        let mut p0: u32 = 0;
        let mut p1: usize = 0;

        assert_eq!(crate::pow::checked_pow(p0, p1), Some(1));
    }
}#[cfg(test)]
mod tests_rug_1018 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u8 = 2;
        let mut p1: u8 = 3;

        <u8 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1019 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 2;
        let mut p1: &u8 = &3;

        <u8 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1020 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 3;
        let mut p1: u8 = 4;

        <&u8 as Pow<u8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1021 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &u8 = &3;
        let p1: &u8 = &4;

        <&u8 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1022 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: u16 = 3;

        <u8 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1023 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u8 = 3;
        let mut p1: &u16 = &4;

        <u8 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1024 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &u8 = &3;
        let p1: u16 = 4;

        <&u8 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1025 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &u8 = &5;
        let p1: &u16 = &3;

        <&u8 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1026 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: u32 = 3;

        <u8 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1027 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: &u32 = &3;

        <u8 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1028 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u8 = &5;
        let mut p1: u32 = 3;

        <&u8 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1029 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u8 = &5;
        let mut p1: &u32 = &3;

        <&'static u8 as Pow<&'static u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1030 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u8 = 3;
        let mut p1: usize = 4;

        <u8 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1031 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: &usize = &3;

        <u8 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1032 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 2;
        let mut p1: usize = 3;

        <&'_ u8 as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1033 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 2;
        let mut p1: usize = 3;

        <&'_ u8 as Pow<&'_ usize>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1034 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: u8 = 3;

        <i8 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1035 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: &u8 = &3;

        <i8 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1036 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &i8 = &3;
        let mut p1: u8 = 2;

        <&i8 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1037 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'static i8 = &2_i8;
        let mut p1: &'static u8 = &3_u8;

        <&'static i8 as Pow<&'static u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1038 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: u16 = 3;

        <i8 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1039 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 3;
        let mut p1: &u16 = &2;

        <i8 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1040 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: u16 = 3;

        <&i8 as Pow<u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1041 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: u16 = 3;

        <&i8 as Pow<&u16>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1042 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: u32 = 3;

        <i8 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1043 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i8 = 2;
        let mut p1: &u32 = &3;

        <i8 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1044 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: u32 = 3;

        <&i8 as Pow<u32>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1045 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: u32 = 3;

        <&i8 as Pow<&u32>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1046 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i8 = 3;
        let mut p1: usize = 4;

        <i8 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1047 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i8 = 3;
        let mut p1: &usize = &2;

        <i8 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1048 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 3;
        let mut p1: usize = 2;

        <&i8 as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1049 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 2;
        let mut p1: usize = 3;

        <&i8 as Pow<&usize>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1050 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u16 = 5;
        let mut p1: u8 = 3;

        <u16 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1051 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u16 = 4;
        let mut p1: &u8 = &2;

        <u16 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1052 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u16 = &42;
        let mut p1: u8 = 3;

        <&u16 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1054 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 2;
        let mut p1: u16 = 3;

        <u16 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1055 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: &u16 = &3;

        <u16 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1056 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 4;
        let mut p1: u16 = 3;

        <&u16 as Pow<u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1057 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 4;
        let mut p1: &'_ u16 = &3;

        <&'_ u16 as Pow<&'_ u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1058 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: u32 = 3;

        <u16 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1059 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: &u32 = &3;

        <u16 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1060 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: u32 = 3;

        <&u16 as Pow<u32>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1061 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &u16 = &5;
        let p1: &u32 = &3;

        <&'static u16 as Pow<&'static u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1062 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: usize = 3;

        <u16 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1063 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: &usize = &3;

        <u16 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1064 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 4;
        let mut p1: usize = 3;

        <&'_ u16 as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1065 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u16 = &4;
        let mut p1: &usize = &3;

        <&u16 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1066 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: u8 = 3;

        <i16 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1067 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: &u8 = &3;

        <i16 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1069 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: u8 = 3;

        <&i16 as Pow<&u8>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1070 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: u16 = 3;

        <i16 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1071 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: &u16 = &3;

        <i16 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1073 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 3;
        let mut p1: u16 = 4;

        <&i16 as Pow<&u16>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1074 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 5;
        let mut p1: u32 = 3;

        <i16 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1075 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i16 = 2;
        let mut p1: &u32 = &3;

        <i16 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1076 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: u32 = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1077 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 3;
        let mut p1: u32 = 4;

        <&i16 as Pow<&u32>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1078 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: usize = 3;

        <i16 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1079 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: &usize = &3;

        <i16 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1080 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i16 = 2;
        let mut p1: usize = 3;

        assert_eq!((&p0).pow(p1), 8);
    }
}#[cfg(test)]
mod tests_rug_1082 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u8 = 3;

        <u32 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1083 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u32 = 4;
        let mut p1: &u8 = &2;

        <u32 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1084 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4;
        let mut p1: u8 = 3;

        <&u32 as Pow<u8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1085 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4;
        let mut p1: u8 = 2;

        <&u32 as Pow<&u8>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1086 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 5;
        let mut p1: u16 = 3;

        <u32 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1087 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4;
        let mut p1: &u16 = &2;

        <u32 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1088 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 5;
        let mut p1: u16 = 3;

        <&u32 as Pow<u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1089 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let base: u32 = 4;
        let exponent: u16 = 3;

        let p0 = &base;
        let p1 = &exponent;

        <&u32 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1090 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 5;
        let mut p1: u32 = 3;

        <u32 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1091 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u32 = 5;
        let mut p1: &u32 = &3;

        <u32 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1092 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u32 = &4;
        let mut p1: u32 = 2;

        <&u32 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1093 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let base: u32 = 5;
        let exponent: u32 = 3;

        let p0 = &base;
        let p1 = &exponent;

        <&u32 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1094 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 5;
        let mut p1: usize = 3;

        <u32 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1095 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 5;
        let mut p1: &usize = &3;

        <u32 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1096 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: &'static u32 = &4;
        let mut p1: usize = 3;

        <&'static u32 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1097 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'static u32 = &4;
        let mut p1: &'static usize = &3;

        <&'static u32 as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1098 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i32 = 4;
        let mut p1: u8 = 3;

        <i32 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1099 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i32 = 2;
        let mut p1: &u8 = &3;

        <i32 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1100 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i32 = 5;
        let mut p1: u8 = 3;

        assert_eq!((&p0).pow(p1), 125);
    }
}#[cfg(test)]
mod tests_rug_1102 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i32 = 2;
        let mut p1: u16 = 3;

        assert_eq!(<i32 as Pow<u16>>::pow(p0, p1), 8);
    }
}#[cfg(test)]
mod tests_rug_1103 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i32 = 2;
        let mut p1: &'_ u16 = &3;

        <i32 as Pow<&'_ u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1104 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i32 = 4;
        let mut p1: u16 = 3;

        <&i32 as Pow<u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1105 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 4;
        let mut p1: u16 = 3;

        <&i32 as Pow<&u16>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1106 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 5;
        let mut p1: u32 = 3;

        <i32 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1107 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2;
        let mut p1: &u32 = &3;

        <i32 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1108 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &i32 = &4;
        let mut p1: u32 = 3;

        <&i32 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1109 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: &i32 = &2;
        let mut p1: &u32 = &3;

        <&i32 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1110 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2;
        let mut p1: usize = 3;

        <i32 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1111 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2;
        let mut p1: &usize = &3;

        <i32 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1112 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i32 = 5;
        let mut p1: usize = 3;

        <&i32 as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1114 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 2;
        let mut p1: u8 = 3;

        <u64 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1115 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 2;
        let mut p1: &u8 = &3;

        <u64 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1116 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u64 = &123;
        let mut p1: u8 = 5;

        <&u64 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1117 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u64 = 2;
        let mut p1: &u8 = &3;

        <&u64 as Pow<&u8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1118 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 4;
        let mut p1: u16 = 3;

        <u64 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1119 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 2;
        let mut p1: &u16 = &3;

        <u64 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1120 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 2;
        let mut p1: u16 = 3;

        <&u64 as Pow<u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1121 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'static u64 = &42;
        let mut p1: &'static u16 = &3;

        <&'static u64 as Pow<&'static u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1122 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u64 = 10;
        let mut p1: u32 = 5;

        <u64 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1123 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u64 = 2;
        let mut p1: &u32 = &3;

        <u64 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1124 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u64 = 10;
        let mut p1: u32 = 3;

        assert_eq!(p0.pow(p1), 1000);
    }
}#[cfg(test)]
mod tests_rug_1125 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u64 = &12345;
        let mut p1: &u32 = &3;

        <&u64 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1126 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 2;
        let mut p1: usize = 3;

        <u64 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1127 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u64 = 2;
        let mut p1: &usize = &3;

        <u64 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1128 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: &'static u64 = &42;
        let mut p1: usize = 3;

        <&'static u64 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1129 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u64 = &42;
        let mut p1: &usize = &3;

        <&u64 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1130 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: u8 = 3;

        <i64 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1131 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: &u8 = &3;

        <i64 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1132 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: u8 = 3;

        assert_eq!(<&i64 as Pow<u8>>::pow(&p0, p1), 8);
    }
}#[cfg(test)]
mod tests_rug_1133 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: u8 = 3;

        <&i64 as Pow<&u8>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1134 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: u16 = 3;

        <i64 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1135 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: &u16 = &3;

        <i64 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1136 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: u16 = 3;

        <&i64 as Pow<u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1137 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: &i64 = &42;
        let mut p1: &u16 = &3;

        <&i64 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1138 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: u32 = 3;

        <i64 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1139 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i64 = 2;
        let mut p1: &'_ u32 = &3;

        <i64 as Pow<&'_ u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1140 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: u32 = 3;

        <&i64 as Pow<u32>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1141 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'_ i64 = &4;
        let mut p1: &'_ u32 = &3;

        <&'static i64 as Pow<&'static u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1142 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: usize = 3;

        <i64 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1143 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 2;
        let mut p1: &usize = &3;

        <i64 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1144 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'static i64 = &2;
        let mut p1: usize = 3;

        <&'static i64 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1145 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &'static i64 = &4;
        let p1: &'static usize = &3;

        <&'static i64 as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1146 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;
        let mut p1: u8 = 5;

        <u128 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1147 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u128 = 12345678901234567890123456789012345678;
        let mut p1: &u8 = &5;

        <u128 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1149 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012;
        let mut p1: u8 = 5;

        <&u128 as Pow<&u8>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1150 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 1234567890123456789012345678901234;
        let mut p1: u16 = 3;

        <u128 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1151 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 5;
        let mut p1: &u16 = &3;

        <u128 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1154 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42;
        let mut p1: u32 = 5;

        <u128 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1155 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42;
        let mut p1: &u32 = &5;

        <u128 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1156 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 17;
        let mut p1: u32 = 4;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1157 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u128 = &12345678901234567890123456789012345678;
        let mut p1: &u32 = &10;

        <&'static u128 as Pow<&'static u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1158 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u128 = 3;
        let mut p1: usize = 4;

        <u128 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1159 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: u128 = 5;
        let mut p1: &usize = &3;

        <u128 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1160 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012;
        let mut p1: usize = 5;

        <&u128 as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1161 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &u128 = &12345678901234567890123456789012345678;
        let mut p1: &usize = &5;

        <&u128 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1162 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789;
        let mut p1: u8 = 3;

        <i128 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1163 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i128 = 5;
        let mut p1: &u8 = &3;

        <i128 as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1165 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 2;
        let mut p1: u8 = 3;

        <&i128 as Pow<&u8>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1166 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 12345;
        let mut p1: u16 = 3;

        <i128 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1167 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 5;
        let mut p1: &u16 = &3;

        <i128 as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1168 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'_ i128 = &123456789;
        let mut p1: u16 = 3;

        <&'_ i128 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1169 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789;
        let mut p1: u16 = 10;

        <&i128 as Pow<&u16>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1170 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 2;
        let mut p1: u32 = 3;

        <i128 as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1171 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 7;
        let mut p1: &u32 = &3;

        <i128 as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1172 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i128 = 5;
        let mut p1: u32 = 3;

        <&i128 as Pow<u32>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1174 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: i128 = 5;
        let mut p1: usize = 3;

        <i128 as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1175 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 2;
        let mut p1: &usize = &3;

        <i128 as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1176 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789;
        let mut p1: usize = 3;

        <&i128 as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1177 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &i128 = &42;
        let p1: &usize = &3;

        <&'static i128 as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1178 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: usize = 2;
        let mut p1: u8 = 3;

        <usize as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1179 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 2;
        let mut p1: &u8 = &3;

        <usize as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1180 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 5;
        let mut p1: u8 = 3;

        <&usize as Pow<u8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1181 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'static usize = &42;
        let mut p1: &'static u8 = &3;

        <&usize as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1182 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 2;
        let mut p1: u16 = 3;

        <usize as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1183 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;
        let mut p1: &u16 = &5;

        <usize as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1184 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &usize = &2;
        let mut p1: u16 = 3;

        <&usize as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1185 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &usize = &42;
        let mut p1: &u16 = &3;

        <&'static usize as Pow<&'static u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1186 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 2;
        let mut p1: u32 = 3;

        <usize as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1187 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let p0: usize = 4;
        let p1: &u32 = &2;

        <usize as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1188 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &usize = &4;
        let p1: u32 = 3;

        <&usize as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1189 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &'static usize = &4;
        let mut p1: &'static u32 = &3;

        <&'static usize as Pow<&'static u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1190 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 4;
        let mut p1: usize = 3;

        <usize as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1191 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 4;
        let mut p1: &usize = &2;

        <usize as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1192 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: usize = 3;
        let mut p1: usize = 4;

        <&usize as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1193 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &usize = &4;
        let p1: &&usize = &&3;

        <&'static usize as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1194 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 2;
        let mut p1: u8 = 3;

        <isize as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1195 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 2;
        let mut p1: &u8 = &3;

        <isize as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1196 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 2;
        let mut p1: u8 = 3;

        <&isize as Pow<u8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1198 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 2;
        let mut p1: u16 = 3;

        <isize as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1199 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 5;
        let mut p1: &u16 = &3;

        <isize as Pow<&u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1200 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 4;
        let mut p1: u16 = 3;

        <&isize as Pow<u16>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1201 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 2;
        let mut p1: u16 = 3;

        <&isize as Pow<&u16>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1202 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 2;
        let mut p1: u32 = 3;

        <isize as Pow<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1203 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 5;
        let mut p1: &u32 = &3;

        <isize as Pow<&u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1204 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: isize = 2;
        let mut p1: u32 = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1205 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 2;
        let mut p1: u32 = 3;

        <&isize as Pow<&u32>>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1206 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = -3;
        let mut p1: usize = 4;

        <isize as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1207 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: isize = 3;
        let mut p1: &usize = &4;

        <isize as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1208 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: isize = 3;
        let mut p1: usize = 4;

        <&isize as Pow<usize>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1209 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &isize = &2;
        let p1: &usize = &3;

        <&'static isize as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1210 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u8> = Wrapping(5);
        let mut p1: u8 = 3;

        <core::num::Wrapping<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1211 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u8> = Wrapping(3);
        let mut p1: &u8 = &4;

        <core::num::Wrapping<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1212 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u8> = &Wrapping(5u8);
        let mut p1: u8 = 3;

        <&'static core::num::Wrapping<u8> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1213 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &Wrapping<u8> = &Wrapping(5u8);
        let mut p1: &u8 = &3u8;

        <&Wrapping<u8> as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1214 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<u8> = core::num::Wrapping(5);
        let mut p1: usize = 3;

        <core::num::Wrapping<u8> as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1215 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u8> = Wrapping(5);
        let mut p1: &usize = &3;

        <Wrapping<u8> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1216 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &Wrapping<u8> = &Wrapping(5u8);
        let mut p1: usize = 3usize;

        <&Wrapping<u8> as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1217 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &Wrapping<u8> = &Wrapping(5u8);
        let mut p1: &usize = &3usize;

        <&Wrapping<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1218 {
    use super::*;
    use crate::Pow;
    
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i8> = core::num::Wrapping(3);
        let mut p1: u8 = 4;

        <core::num::Wrapping<i8> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1219 {
    use super::*;
    use crate::Pow;
    
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i8> = core::num::Wrapping(5);
        let mut p1: &u8 = &3;

        <core::num::Wrapping<i8> as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1220 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i8> = Wrapping(5);
        let mut p1: u8 = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1221 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i8> = &core::num::Wrapping(3);
        let mut p1: &u8 = &2;

        <&'static core::num::Wrapping<i8> as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1222 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i8> = core::num::Wrapping(3);
        let mut p1: usize = 4;

        <core::num::Wrapping<i8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1223 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i8> = core::num::Wrapping(3);
        let mut p1: &usize = &4;

        <core::num::Wrapping<i8> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1224 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i8> = core::num::Wrapping(5);
        let mut p1: usize = 3;

        <&core::num::Wrapping<i8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1225 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i8> = &Wrapping(3_i8);
        let mut p1: &&usize = &&2_usize;

        <&'static core::num::Wrapping<i8> as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1226 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u16> = Wrapping(5);
        let mut p1: u8 = 3;

        <core::num::Wrapping<u16> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1227 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<u16> = core::num::Wrapping(5);
        let mut p1: &'static u8 = &3;

        <core::num::Wrapping<u16> as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1228 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u16> = &Wrapping(5);
        let mut p1: u8 = 3;

        <&'static core::num::Wrapping<u16> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1229 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<u16> = core::num::Wrapping(42);
        let mut p1: &u8 = &3;

        <&core::num::Wrapping<u16> as Pow<&u8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1230 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u16> = Wrapping(123);
        let mut p1: usize = 5;

        <core::num::Wrapping<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1231 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u16> = Wrapping(42);
        let mut p1: &usize = &3;

        <Wrapping<u16> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1232 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u16> = &Wrapping(5);
        let mut p1: usize = 3;

        <&'static core::num::Wrapping<u16> as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1233 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u16> = &Wrapping(5u16);
        let mut p1: &usize = &3;

        <&'static core::num::Wrapping<u16> as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1234 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i16> = Wrapping(5);
        let mut p1: u8 = 3;

        <core::num::Wrapping<i16> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1235 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i16> = core::num::Wrapping(5);
        let mut p1: &u8 = &3;

        <core::num::Wrapping<i16> as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1236 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i16> = Wrapping(5);
        let mut p1: u8 = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1237 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i16> = &Wrapping(5);
        let mut p1: &u8 = &3;

        <&'static core::num::Wrapping<i16> as Pow<&'_ u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1238 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i16> = core::num::Wrapping(3);
        let mut p1: usize = 4;

        <core::num::Wrapping<i16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1239 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i16> = core::num::Wrapping(3);
        let mut p1: &usize = &2;

        <core::num::Wrapping<i16> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1240 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i16> = &Wrapping(3);
        let mut p1: usize = 4;

        <&'static core::num::Wrapping<i16> as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1241 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i16> = &core::num::Wrapping(3);
        let mut p1: &usize = &4;

        <&'static core::num::Wrapping<i16> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1242 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42u32);
        let mut p1: u8 = 5;

        <core::num::Wrapping<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1243 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42u32);
        let mut p1: &u8 = &5;

        <core::num::Wrapping<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1244 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42u32);
        let mut p1: u8 = 5u8;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1245 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u32> = &Wrapping(42u32);
        let mut p1: &u8 = &5u8;

        <&'static core::num::Wrapping<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1246 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42u32);
        let mut p1: usize = 5;

        <core::num::Wrapping<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1247 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42u32);
        let mut p1: &usize = &5;

        <core::num::Wrapping<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1248 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42u32);
        let mut p1: usize = 5;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1249 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u32> = &Wrapping(42u32);
        let mut p1: &usize = &5;

        <&'static core::num::Wrapping<u32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1250 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i32> = core::num::Wrapping::<i32>(42);
        let mut p1: u8 = 5;

        <core::num::Wrapping<i32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1251 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i32> = core::num::Wrapping::<i32>(42);
        let mut p1: &'static u8 = &3;

        <core::num::Wrapping<i32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1252 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i32> = core::num::Wrapping::<i32>(42);
        let mut p1: u8 = 5;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1253 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i32> = &core::num::Wrapping::<i32>(42); // create the local variable v13 with type core::num::Wrapping<i32>
        let mut p1: &u8 = &3; // sample data for u8

        <&'static core::num::Wrapping<i32> as Pow<&'static u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1254 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: core::num::Wrapping<i32> = core::num::Wrapping::<i32>(42);
        let mut p1: usize = 5;

        <core::num::Wrapping<i32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1255 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping::<i32>(42);
        let mut p1: &usize = &3;

        <Wrapping<i32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1256 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i32> = core::num::Wrapping::<i32>(42);
        let mut p1: usize = 5;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1257 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping::<i32>(42); // create the local variable with type core::num::Wrapping<i32>
        let mut p1: usize = 5; // sample data for usize

        p0.pow(&p1);
    }
}#[cfg(test)]
mod tests_rug_1258 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u64> = Wrapping(1234567890u64);
        let mut p1: u8 = 3;

        <core::num::Wrapping<u64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1259 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u64> = Wrapping(1234567890u64);
        let mut p1: &u8 = &3; // Sample data for u8

        <Wrapping<u64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1260 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u64> = &Wrapping(1234567890u64);
        let mut p1: u8 = 3;

        <&core::num::Wrapping<u64> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1261 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u64> = &Wrapping(1234567890u64);
        let mut p1: &u8 = &3; // Example value for u8

        <&'static core::num::Wrapping<u64> as Pow<&'static u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1262 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u64> = Wrapping(1234567890u64);
        let mut p1: usize = 3;

        <core::num::Wrapping<u64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1263 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u64> = Wrapping(1234567890u64);
        let mut p1: &usize = &3; // sample data for usize

        <core::num::Wrapping<u64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1264 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u64> = Wrapping(1234567890u64);
        let mut p1: usize = 5;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1265 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u64> = Wrapping(1234567890u64);
        let mut p1: &usize = &3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1266 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i64> = core::num::Wrapping(42i64);
        let mut p1: u8 = 3;

        <core::num::Wrapping<i64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1267 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i64> = core::num::Wrapping(42i64);
        let mut p1: &u8 = &3u8;

        <core::num::Wrapping<i64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1268 {
    use super::*;
    use crate::Pow;
    
    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i64> = &core::num::Wrapping(42i64);
        let mut p1: u8 = 5;

        <&core::num::Wrapping<i64> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1269 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i64> = Wrapping(42i64); // create the local variable with type core::num::Wrapping<i64>
        let mut p1: &u8 = &3; // sample data for u8

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1270 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i64> = core::num::Wrapping(42i64);
        let mut p1: usize = 3;

        <core::num::Wrapping<i64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1271 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<i64> = core::num::Wrapping(42i64);
        let mut p1: &usize = &3; // Sample data for usize

        <core::num::Wrapping<i64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1272 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i64> = Wrapping(42i64);
        let mut p1: usize = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1273 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0 = &core::num::Wrapping(42i64);
        let mut p1 = &3usize;

        <&'static core::num::Wrapping<i64> as Pow<&'static usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1274 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u128> = Wrapping(42u128);
        let mut p1: u8 = 3;

        <core::num::Wrapping<u128>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1275 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u128> = Wrapping(42u128);
        let mut p1: &u8 = &3;

        <core::num::Wrapping<u128>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1276 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u128> = Wrapping(42u128);
        let mut p1: u8 = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1277 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<u128> = &Wrapping(42u128);
        let mut p1: &u8 = &3u8;

        <&core::num::Wrapping<u128> as Pow<&u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1278 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u128> = Wrapping(42u128);
        let mut p1: usize = 3;

        <core::num::Wrapping<u128>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1279 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u128> = Wrapping(42u128);
        let mut p1: &usize = &3;

        <core::num::Wrapping<u128> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1280 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u128> = Wrapping(42u128);
        let mut p1: usize = 3; // Example value for usize

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1281 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u128> = Wrapping(42u128);
        let mut p1: &usize = &3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1282 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i128> = Wrapping(42_i128);
        let mut p1: u8 = 3;

        <core::num::Wrapping<i128>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1283 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i128> = Wrapping(42_i128);
        let mut p1: &u8 = &3_u8;

        <core::num::Wrapping<i128>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1284 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i128> = Wrapping(42_i128);
        let mut p1: u8 = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1285 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &Wrapping<i128> = &Wrapping(42_i128);
        let mut p1: &u8 = &3_u8;

        <&'static Wrapping<i128>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1286 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i128> = Wrapping(42_i128);
        let mut p1: usize = 5;

        <core::num::Wrapping<i128>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1287 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i128> = Wrapping(42_i128);
        let mut p1: &usize = &3;

        <Wrapping<i128> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1288 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i128> = Wrapping(42_i128);
        let mut p1: usize = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1289 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<i128> = &Wrapping(42_i128);
        let p1: &usize = &3;

        <&'static core::num::Wrapping<i128> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1290 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<usize> = core::num::Wrapping(42usize);
        let mut p1: u8 = 3;

        <core::num::Wrapping<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1291 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<usize> = core::num::Wrapping(42usize);
        let mut p1: &u8 = &3; // Sample data for u8

        <core::num::Wrapping<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1292 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<usize> = &core::num::Wrapping(42usize);
        let mut p1: u8 = 3;

        <&core::num::Wrapping<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1293 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<usize> = &Wrapping(42usize);
        let mut p1: &u8 = &3;

        <&'static core::num::Wrapping<usize> as Pow<&'_ u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1294 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<usize> = core::num::Wrapping(42usize);
        let mut p1: usize = 5;

        <core::num::Wrapping<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1295 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<usize> = core::num::Wrapping(42usize);
        let mut p1: &usize = &3; // Sample data for the second argument

        <core::num::Wrapping<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1296 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<usize> = Wrapping(42usize);
        let mut p1: usize = 5;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1297 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<usize> = &core::num::Wrapping(42usize);
        let mut p1: &usize = &5;

        <&'static core::num::Wrapping<usize> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1298 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<isize> = core::num::Wrapping(123);
        let mut p1: u8 = 4;

        <core::num::Wrapping<isize> as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1299 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<isize> = core::num::Wrapping(3);
        let mut p1: u8 = 4;

        <core::num::Wrapping<isize> as Pow<&u8>>::pow(p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1300 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<isize> = Wrapping(5);
        let mut p1: u8 = 3;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1301 {
    use super::*;
    use crate::Pow;
    #[test]
    fn test_rug() {
        let mut p0: core::num::Wrapping<isize> = core::num::Wrapping(5);
        let mut p1: &u8 = &3;

        <&core::num::Wrapping<isize> as Pow<&u8>>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1302 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<isize> = Wrapping(3);
        let mut p1: usize = 4;

        <Wrapping<isize> as Pow<usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1303 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<isize> = Wrapping(5);
        let mut p1: &usize = &3;

        <Wrapping<isize> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1304 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<isize> = Wrapping(3);
        let mut p1: usize = 4;

        p0.pow(p1);
    }
}#[cfg(test)]
mod tests_rug_1305 {
    use super::*;
    use crate::Pow;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: &core::num::Wrapping<isize> = &Wrapping(3);
        let mut p1: &usize = &4;

        <&'static Wrapping<isize> as Pow<&usize>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1306 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f32 = 2.5;
        let mut p1: i8 = 3;

        <f32 as Pow<i8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1307 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.5;
        let mut p1: &i8 = &3;

        <f32 as Pow<&i8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1308 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f32 = 2.0;
        let mut p1: i8 = 3;

        <&f32>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1309 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f32 = &3.5;
        let mut p1: &i8 = &2;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1310 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f32 = 2.0;
        let mut p1: u8 = 3;

        <f32 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1311 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.0;
        let mut p1: u8 = 3;

        <f32 as Pow<&u8>>::pow(p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1312 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let p0: &f32 = &2.0;
        let p1: u8 = 3;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1313 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f32 = &2.0;
        let mut p1: &u8 = &3;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1314 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.5;
        let mut p1: i16 = 3;

        <f32 as Pow<i16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1315 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f32 = 2.5;
        let mut p1: &i16 = &2;

        <f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1316 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f32 = &2.5;
        let mut p1: i16 = 3;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1317 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f32 = &2.5;
        let mut p1: &'static i16 = &3;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1318 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f32 = 2.5;
        let mut p1: u16 = 3;

        <f32 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1319 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.5;
        let mut p1: &u16 = &3;

        <f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1320 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &f32 = &2.5;
        let p1: u16 = 3;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1321 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.0;
        let mut p1: u16 = 3;

        <&f32>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1322 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.5;
        let mut p1: i32 = 3;

        <f32 as Pow<i32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1323 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f32 = 2.0;
        let mut p1: &i32 = &3;

        <f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1324 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f32 = &3.5;
        let mut p1: i32 = 2;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1325 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.5;
        let mut p1: i32 = 3;

        <&f32>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1326 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.0;
        let mut p1: i8 = 3;

        <f64 as Pow<i8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1327 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: &i8 = &3;

        <f64 as Pow<&i8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1328 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: i8 = 3;

        <&f64>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1329 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: &f64 = &2.5;
        let mut p1: &i8 = &3;

        <&f64>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1330 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: u8 = 3;

        <f64 as Pow<u8>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1331 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.5;
        let mut p1: u8 = 3;

        <f64 as Pow<&u8>>::pow(p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1332 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: u8 = 3;

        <&f64>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1333 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: u8 = 3;

        <&f64>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1334 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: i16 = 3;

        <f64 as Pow<i16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1335 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: &i16 = &3;

        <f64 as Pow<&i16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1336 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: i16 = 3;

        <&f64>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1337 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.5;
        let mut p1: i16 = 3;

        <&f64>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1338 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.5;
        let mut p1: u16 = 3;

        <f64 as Pow<u16>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1339 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: u16 = 3;

        <f64>::pow(p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1340 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: u16 = 3;

        <&f64>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1341 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: u16 = 3;

        <&f64>::pow(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1342 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.5;
        let mut p1: i32 = 3;

        <f64>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1343 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.5;
        let mut p1: &i32 = &3;

        <f64 as Pow<&i32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1344 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: i32 = 3;

        <&f64>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1345 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let p0: &f64 = &2.5;
        let p1: &i32 = &3;

        <&f64>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1346 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.0;
        let mut p1: f32 = 3.0;

        <f32 as Pow<f32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1347 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.0;
        let mut p1: &f32 = &3.0;

        <f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1348 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f32 = &2.0;
        let mut p1: f32 = 3.0;

        <&f32>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1349 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 2.0;
        let mut p1: &f32 = &3.0;

        <&f32>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1350 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: f32 = 3.5;

        <f64 as Pow<f32>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1351 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: &f32 = &3.0;

        <f64>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1352 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f64 = &2.0;
        let mut p1: f32 = 3.0;

        <&f64>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1353 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: &f64 = &2.0;
        let mut p1: &f32 = &3.0;

        <&f64>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1354 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.0;
        let mut p1: f64 = 3.0;

        <f64 as Pow<f64>>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1355 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 2.0;
        let mut p1: &f64 = &3.0;

        <f64>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1356 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.0;
        let mut p1: f64 = 3.0;

        <&f64>::pow(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1357 {
    use super::*;
    use crate::Pow;

    #[test]
    fn test_pow() {
        let mut p0: f64 = 2.0;
        let mut p1: &f64 = &3.0;

        <&f64>::pow(&p0, p1);
    }
}