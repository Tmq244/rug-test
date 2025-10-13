use core::ops::{Div, Rem};

pub trait Euclid: Sized + Div<Self, Output = Self> + Rem<Self, Output = Self> {
    /// Calculates Euclidean division, the matching method for `rem_euclid`.
    ///
    /// This computes the integer `n` such that
    /// `self = n * v + self.rem_euclid(v)`.
    /// In other words, the result is `self / v` rounded to the integer `n`
    /// such that `self >= n * v`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::Euclid;
    ///
    /// let a: i32 = 7;
    /// let b: i32 = 4;
    /// assert_eq!(Euclid::div_euclid(&a, &b), 1); // 7 > 4 * 1
    /// assert_eq!(Euclid::div_euclid(&-a, &b), -2); // -7 >= 4 * -2
    /// assert_eq!(Euclid::div_euclid(&a, &-b), -1); // 7 >= -4 * -1
    /// assert_eq!(Euclid::div_euclid(&-a, &-b), 2); // -7 >= -4 * 2
    /// ```
    fn div_euclid(&self, v: &Self) -> Self;

    /// Calculates the least nonnegative remainder of `self (mod v)`.
    ///
    /// In particular, the return value `r` satisfies `0.0 <= r < v.abs()` in
    /// most cases. However, due to a floating point round-off error it can
    /// result in `r == v.abs()`, violating the mathematical definition, if
    /// `self` is much smaller than `v.abs()` in magnitude and `self < 0.0`.
    /// This result is not an element of the function's codomain, but it is the
    /// closest floating point number in the real numbers and thus fulfills the
    /// property `self == self.div_euclid(v) * v + self.rem_euclid(v)`
    /// approximatively.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::Euclid;
    ///
    /// let a: i32 = 7;
    /// let b: i32 = 4;
    /// assert_eq!(Euclid::rem_euclid(&a, &b), 3);
    /// assert_eq!(Euclid::rem_euclid(&-a, &b), 1);
    /// assert_eq!(Euclid::rem_euclid(&a, &-b), 3);
    /// assert_eq!(Euclid::rem_euclid(&-a, &-b), 1);
    /// ```
    fn rem_euclid(&self, v: &Self) -> Self;
}

macro_rules! euclid_forward_impl {
    ($($t:ty)*) => {$(
        #[cfg(has_div_euclid)]
        impl Euclid for $t {
            #[inline]
            fn div_euclid(&self, v: &$t) -> Self {
                <$t>::div_euclid(*self, *v)
            }

            #[inline]
            fn rem_euclid(&self, v: &$t) -> Self {
                <$t>::rem_euclid(*self, *v)
            }
        }
    )*}
}

macro_rules! euclid_int_impl {
    ($($t:ty)*) => {$(
        euclid_forward_impl!($t);

        #[cfg(not(has_div_euclid))]
        impl Euclid for $t {
            #[inline]
            fn div_euclid(&self, v: &$t) -> Self {
                let q = self / v;
                if self % v < 0 {
                    return if *v > 0 { q - 1 } else { q + 1 }
                }
                q
            }

            #[inline]
            fn rem_euclid(&self, v: &$t) -> Self {
                let r = self % v;
                if r < 0 {
                    if *v < 0 {
                        r - v
                    } else {
                        r + v
                    }
                } else {
                    r
                }
            }
        }
    )*}
}

macro_rules! euclid_uint_impl {
    ($($t:ty)*) => {$(
        euclid_forward_impl!($t);

        #[cfg(not(has_div_euclid))]
        impl Euclid for $t {
            #[inline]
            fn div_euclid(&self, v: &$t) -> Self {
                self / v
            }

            #[inline]
            fn rem_euclid(&self, v: &$t) -> Self {
                self % v
            }
        }
    )*}
}

euclid_int_impl!(isize i8 i16 i32 i64);
euclid_uint_impl!(usize u8 u16 u32 u64);
#[cfg(has_i128)]
euclid_int_impl!(i128);
#[cfg(has_i128)]
euclid_uint_impl!(u128);

#[cfg(all(has_div_euclid, feature = "std"))]
euclid_forward_impl!(f32 f64);

#[cfg(not(all(has_div_euclid, feature = "std")))]
impl Euclid for f32 {
    #[inline]
    fn div_euclid(&self, v: &f32) -> f32 {
        let q = <f32 as ::float::FloatCore>::trunc(self / v);
        if self % v < 0.0 {
            return if *v > 0.0 { q - 1.0 } else { q + 1.0 };
        }
        q
    }

    #[inline]
    fn rem_euclid(&self, v: &f32) -> f32 {
        let r = self % v;
        if r < 0.0 {
            r + <f32 as ::float::FloatCore>::abs(*v)
        } else {
            r
        }
    }
}

#[cfg(not(all(has_div_euclid, feature = "std")))]
impl Euclid for f64 {
    #[inline]
    fn div_euclid(&self, v: &f64) -> f64 {
        let q = <f64 as ::float::FloatCore>::trunc(self / v);
        if self % v < 0.0 {
            return if *v > 0.0 { q - 1.0 } else { q + 1.0 };
        }
        q
    }

    #[inline]
    fn rem_euclid(&self, v: &f64) -> f64 {
        let r = self % v;
        if r < 0.0 {
            r + <f64 as ::float::FloatCore>::abs(*v)
        } else {
            r
        }
    }
}

pub trait CheckedEuclid: Euclid {
    /// Performs euclid division that returns `None` instead of panicking on division by zero
    /// and instead of wrapping around on underflow and overflow.
    fn checked_div_euclid(&self, v: &Self) -> Option<Self>;

    /// Finds the euclid remainder of dividing two numbers, checking for underflow, overflow and
    /// division by zero. If any of that happens, `None` is returned.
    fn checked_rem_euclid(&self, v: &Self) -> Option<Self>;
}

macro_rules! checked_euclid_forward_impl {
    ($($t:ty)*) => {$(
        #[cfg(has_div_euclid)]
        impl CheckedEuclid for $t {
            #[inline]
            fn checked_div_euclid(&self, v: &$t) -> Option<Self> {
                <$t>::checked_div_euclid(*self, *v)
            }

            #[inline]
            fn checked_rem_euclid(&self, v: &$t) -> Option<Self> {
                <$t>::checked_rem_euclid(*self, *v)
            }
        }
    )*}
}

macro_rules! checked_euclid_int_impl {
    ($($t:ty)*) => {$(
        checked_euclid_forward_impl!($t);

        #[cfg(not(has_div_euclid))]
        impl CheckedEuclid for $t {
            #[inline]
            fn checked_div_euclid(&self, v: &$t) -> Option<$t> {
                if *v == 0 || (*self == Self::min_value() && *v == -1) {
                    None
                } else {
                    Some(Euclid::div_euclid(self, v))
                }
            }

            #[inline]
            fn checked_rem_euclid(&self, v: &$t) -> Option<$t> {
                if *v == 0 || (*self == Self::min_value() && *v == -1) {
                    None
                } else {
                    Some(Euclid::rem_euclid(self, v))
                }
            }
        }
    )*}
}

macro_rules! checked_euclid_uint_impl {
    ($($t:ty)*) => {$(
        checked_euclid_forward_impl!($t);

        #[cfg(not(has_div_euclid))]
        impl CheckedEuclid for $t {
            #[inline]
            fn checked_div_euclid(&self, v: &$t) -> Option<$t> {
                if *v == 0 {
                    None
                } else {
                    Some(Euclid::div_euclid(self, v))
                }
            }

            #[inline]
            fn checked_rem_euclid(&self, v: &$t) -> Option<$t> {
                if *v == 0 {
                    None
                } else {
                    Some(Euclid::rem_euclid(self, v))
                }
            }
        }
    )*}
}

checked_euclid_int_impl!(isize i8 i16 i32 i64);
checked_euclid_uint_impl!(usize u8 u16 u32 u64);
#[cfg(has_i128)]
checked_euclid_int_impl!(i128);
#[cfg(has_i128)]
checked_euclid_uint_impl!(u128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn euclid_unsigned() {
        macro_rules! test_euclid {
            ($($t:ident)+) => {
                $(
                    {
                        let x: $t = 10;
                        let y: $t = 3;
                        assert_eq!(Euclid::div_euclid(&x, &y), 3);
                        assert_eq!(Euclid::rem_euclid(&x, &y), 1);
                    }
                )+
            };
        }

        test_euclid!(usize u8 u16 u32 u64);
    }

    #[test]
    fn euclid_signed() {
        macro_rules! test_euclid {
            ($($t:ident)+) => {
                $(
                    {
                        let x: $t = 10;
                        let y: $t = -3;
                        assert_eq!(Euclid::div_euclid(&x, &y), -3);
                        assert_eq!(Euclid::div_euclid(&-x, &y), 4);
                        assert_eq!(Euclid::rem_euclid(&x, &y), 1);
                        assert_eq!(Euclid::rem_euclid(&-x, &y), 2);
                        let x: $t = $t::min_value() + 1;
                        let y: $t = -1;
                        assert_eq!(Euclid::div_euclid(&x, &y), $t::max_value());
                    }
                )+
            };
        }

        test_euclid!(isize i8 i16 i32 i64);
    }

    #[test]
    fn euclid_float() {
        macro_rules! test_euclid {
            ($($t:ident)+) => {
                $(
                    {
                        let x: $t = 12.1;
                        let y: $t = 3.2;
                        assert!(Euclid::div_euclid(&x, &y) * y + Euclid::rem_euclid(&x, &y) - x
                        <= 46.4 * <$t as ::float::FloatCore>::epsilon());
                        assert!(Euclid::div_euclid(&x, &-y) * -y + Euclid::rem_euclid(&x, &-y) - x
                        <= 46.4 * <$t as ::float::FloatCore>::epsilon());
                        assert!(Euclid::div_euclid(&-x, &y) * y + Euclid::rem_euclid(&-x, &y) + x
                        <= 46.4 * <$t as ::float::FloatCore>::epsilon());
                        assert!(Euclid::div_euclid(&-x, &-y) * -y + Euclid::rem_euclid(&-x, &-y) + x
                        <= 46.4 * <$t as ::float::FloatCore>::epsilon());
                    }
                )+
            };
        }

        test_euclid!(f32 f64);
    }

    #[test]
    fn euclid_checked() {
        macro_rules! test_euclid_checked {
            ($($t:ident)+) => {
                $(
                    {
                        assert_eq!(CheckedEuclid::checked_div_euclid(&$t::min_value(), &-1), None);
                        assert_eq!(CheckedEuclid::checked_rem_euclid(&$t::min_value(), &-1), None);
                        assert_eq!(CheckedEuclid::checked_div_euclid(&1, &0), None);
                        assert_eq!(CheckedEuclid::checked_rem_euclid(&1, &0), None);
                    }
                )+
            };
        }

        test_euclid_checked!(isize i8 i16 i32 i64);
    }
}
#[cfg(test)]
mod tests_rug_1599 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: isize = 5;

        <isize as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1600 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: isize = 7;
        let mut p1: isize = 3;

        <isize as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1601 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 15;
        let mut p1: i8 = 6;

        <i8 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1602 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 13;
        let mut p1: i8 = 5;

        assert_eq!(<i8 as Euclid>::rem_euclid(&p0, &p1), 3);
    }
}#[cfg(test)]
mod tests_rug_1603 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;
        let mut p1: i16 = 5;

        <i16 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1604 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 15;
        let mut p1: i16 = 4;

        assert_eq!(<i16 as Euclid>::rem_euclid(&p0, &p1), 3);
    }
}#[cfg(test)]
mod tests_rug_1605 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 17;
        let mut p1: i32 = 4;

        <i32 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1606 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 17;
        let mut p1: i32 = 5;

        <i32 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1607 {
    use super::*;
    use crate::ops::euclid::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 15;
        let mut p1: i64 = 4;

        let result = <i64 as Euclid>::div_euclid(&p0, &p1);
        assert_eq!(result, 3);
    }
}#[cfg(test)]
mod tests_rug_1608 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 17;
        let mut p1: i64 = 5;

        <i64 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1609 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 3;

        <usize as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1610 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 3;

        <usize as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1611 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 3;

        <u8 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1612 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 3;

        <u8 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1613 {
    use super::*;
    use crate::ops::euclid::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;
        let mut p1: u16 = 5;

        let result = <u16 as Euclid>::div_euclid(&p0, &p1);
        assert_eq!(result, 8); // 42 div_euclid 5 is 8
    }
}#[cfg(test)]
mod tests_rug_1614 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 45;
        let mut p1: u16 = 12;

        <u16 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1615 {
    use super::*;
    use crate::ops::euclid::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 3;

        <u32 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1616 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 17;
        let mut p1: u32 = 5;

        <u32 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1617 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 17;
        let mut p1: u64 = 3;

        <u64 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1618 {
    use super::*;
    use crate::ops::euclid::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 42;
        let mut p1: u64 = 5;

        <u64 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1619 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: i128 = 5;

        <i128 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1620 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 75;
        let mut p1: i128 = 6;

        <i128 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1621 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;
        let mut p1: u128 = 98765432109876543210987654321098765432;

        <u128 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1622 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;
        let mut p1: u128 = 98765432109876543210987654321;

        <u128 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1623 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 15.5;
        let mut p1: f32 = 4.0;

        <f32 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1624 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 10.5;
        let mut p1: f32 = 3.2;

        <f32 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1625 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 7.5;
        let mut p1: f64 = 2.3;

        <f64 as Euclid>::div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1626 {
    use super::*;
    use crate::Euclid;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 7.5;
        let mut p1: f64 = 2.3;

        <f64 as Euclid>::rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1627 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: isize = 7;

        <isize as CheckedEuclid>::checked_div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1628 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: isize = 5;

        <isize as CheckedEuclid>::checked_rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1629 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 3;

        let result = <i8 as CheckedEuclid>::checked_div_euclid(&p0, &p1);
        assert_eq!(result, Some(3));
    }
}#[cfg(test)]
mod tests_rug_1630 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 3;

        assert_eq!(<i8 as CheckedEuclid>::checked_rem_euclid(&p0, &p1), Some(1));
    }
}#[cfg(test)]
mod tests_rug_1631 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 15;
        let mut p1: i16 = 4;

        assert_eq!(<i16 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(3));
    }

    #[test]
    fn test_rug_zero_divisor() {
        let mut p0: i16 = 15;
        let mut p1: i16 = 0;

        assert_eq!(<i16 as CheckedEuclid>::checked_div_euclid(&p0, &p1), None);
    }

    #[test]
    fn test_rug_negative_dividend() {
        let mut p0: i16 = -15;
        let mut p1: i16 = 4;

        assert_eq!(<i16 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(-4));
    }

    #[test]
    fn test_rug_negative_divisor() {
        let mut p0: i16 = 15;
        let mut p1: i16 = -4;

        assert_eq!(<i16 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(-4));
    }

    #[test]
    fn test_rug_both_negative() {
        let mut p0: i16 = -15;
        let mut p1: i16 = -4;

        assert_eq!(<i16 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(3));
    }
}#[cfg(test)]
mod tests_rug_1632 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 27;
        let mut p1: i16 = 5;

        assert_eq!(<i16 as CheckedEuclid>::checked_rem_euclid(&p0, &p1), Some(2));
    }
}#[cfg(test)]
mod tests_rug_1633 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 3;

        <i32 as CheckedEuclid>::checked_div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1634 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 17;
        let mut p1: i32 = 4;

        assert_eq!(<i32 as CheckedEuclid>::checked_rem_euclid(&p0, &p1), Some(1));
    }
}#[cfg(test)]
mod tests_rug_1635 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 15;
        let mut p1: i64 = 4;

        assert_eq!(<i64 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(3));
        
        // Test with zero divisor
        let p2: i64 = 0;
        assert_eq!(<i64 as CheckedEuclid>::checked_div_euclid(&p0, &p2), None);
        
        // Test with negative numbers
        let p3: i64 = -15;
        let p4: i64 = 4;
        assert_eq!(<i64 as CheckedEuclid>::checked_div_euclid(&p3, &p4), Some(-4));
        
        // Test with zero dividend
        let p5: i64 = 0;
        assert_eq!(<i64 as CheckedEuclid>::checked_div_euclid(&p5, &p1), Some(0));
    }
}#[cfg(test)]
mod tests_rug_1636 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 17;
        let mut p1: i64 = 5;

        assert_eq!(<i64 as CheckedEuclid>::checked_rem_euclid(&p0, &p1), Some(2));
    }
}#[cfg(test)]
mod tests_rug_1637 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;
        let mut p1: usize = 5;

        <usize as CheckedEuclid>::checked_div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1638 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: usize = 15;
        let mut p1: usize = 4;

        <usize as CheckedEuclid>::checked_rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1639 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 255;
        let mut p1: u8 = 3;

        assert_eq!(<u8 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(85));
        
        // Test division by zero
        let p2: u8 = 0;
        assert_eq!(<u8 as CheckedEuclid>::checked_div_euclid(&p0, &p2), None);
    }
}#[cfg(test)]
mod tests_rug_1640 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 3;

        <u8 as CheckedEuclid>::checked_rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1641 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;
        let mut p1: u16 = 7;

        assert_eq!(<u16 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(6));
        
        // Test division by zero
        p1 = 0;
        assert_eq!(<u16 as CheckedEuclid>::checked_div_euclid(&p0, &p1), None);
    }
}#[cfg(test)]
mod tests_rug_1642 {
    use super::*;
    use crate::ops::euclid::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 25;
        let mut p1: u16 = 7;

        <u16 as CheckedEuclid>::checked_rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1643 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 3;

        <u32 as CheckedEuclid>::checked_div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1644 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 17;
        let mut p1: u32 = 5;

        assert_eq!(<u32 as CheckedEuclid>::checked_rem_euclid(&p0, &p1), Some(2));
    }
}#[cfg(test)]
mod tests_rug_1645 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 42;
        let mut p1: u64 = 5;

        assert_eq!(<u64 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(8));
    }
}#[cfg(test)]
mod tests_rug_1646 {
    use super::*;
    use crate::ops::euclid::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;
        let mut p1: u64 = 6789;

        assert_eq!(<u64 as CheckedEuclid>::checked_rem_euclid(&p0, &p1), Some(1761));
    }
}#[cfg(test)]
mod tests_rug_1647 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: i128 = 5;

        <i128 as CheckedEuclid>::checked_div_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1648 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 17;
        let mut p1: i128 = 5;

        <i128 as CheckedEuclid>::checked_rem_euclid(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1649 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42;
        let mut p1: u128 = 7;

        assert_eq!(<u128 as CheckedEuclid>::checked_div_euclid(&p0, &p1), Some(6));
    }
}#[cfg(test)]
mod tests_rug_1650 {
    use super::*;
    use crate::CheckedEuclid;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128
        let mut p1: u128 = 123456789;           // Sample data for u128

        assert_eq!(<u128 as CheckedEuclid>::checked_rem_euclid(&p0, &p1), Some(18446744072464587026));
    }
}