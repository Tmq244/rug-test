use core::ops::{Add, Div, Mul, Rem, Shl, Shr, Sub};

/// Performs addition that returns `None` instead of wrapping around on
/// overflow.
pub trait CheckedAdd: Sized + Add<Self, Output = Self> {
    /// Adds two numbers, checking for overflow. If overflow happens, `None` is
    /// returned.
    fn checked_add(&self, v: &Self) -> Option<Self>;
}

macro_rules! checked_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &$t) -> Option<$t> {
                <$t>::$method(*self, *v)
            }
        }
    };
}

checked_impl!(CheckedAdd, checked_add, u8);
checked_impl!(CheckedAdd, checked_add, u16);
checked_impl!(CheckedAdd, checked_add, u32);
checked_impl!(CheckedAdd, checked_add, u64);
checked_impl!(CheckedAdd, checked_add, usize);
#[cfg(has_i128)]
checked_impl!(CheckedAdd, checked_add, u128);

checked_impl!(CheckedAdd, checked_add, i8);
checked_impl!(CheckedAdd, checked_add, i16);
checked_impl!(CheckedAdd, checked_add, i32);
checked_impl!(CheckedAdd, checked_add, i64);
checked_impl!(CheckedAdd, checked_add, isize);
#[cfg(has_i128)]
checked_impl!(CheckedAdd, checked_add, i128);

/// Performs subtraction that returns `None` instead of wrapping around on underflow.
pub trait CheckedSub: Sized + Sub<Self, Output = Self> {
    /// Subtracts two numbers, checking for underflow. If underflow happens,
    /// `None` is returned.
    fn checked_sub(&self, v: &Self) -> Option<Self>;
}

checked_impl!(CheckedSub, checked_sub, u8);
checked_impl!(CheckedSub, checked_sub, u16);
checked_impl!(CheckedSub, checked_sub, u32);
checked_impl!(CheckedSub, checked_sub, u64);
checked_impl!(CheckedSub, checked_sub, usize);
#[cfg(has_i128)]
checked_impl!(CheckedSub, checked_sub, u128);

checked_impl!(CheckedSub, checked_sub, i8);
checked_impl!(CheckedSub, checked_sub, i16);
checked_impl!(CheckedSub, checked_sub, i32);
checked_impl!(CheckedSub, checked_sub, i64);
checked_impl!(CheckedSub, checked_sub, isize);
#[cfg(has_i128)]
checked_impl!(CheckedSub, checked_sub, i128);

/// Performs multiplication that returns `None` instead of wrapping around on underflow or
/// overflow.
pub trait CheckedMul: Sized + Mul<Self, Output = Self> {
    /// Multiplies two numbers, checking for underflow or overflow. If underflow
    /// or overflow happens, `None` is returned.
    fn checked_mul(&self, v: &Self) -> Option<Self>;
}

checked_impl!(CheckedMul, checked_mul, u8);
checked_impl!(CheckedMul, checked_mul, u16);
checked_impl!(CheckedMul, checked_mul, u32);
checked_impl!(CheckedMul, checked_mul, u64);
checked_impl!(CheckedMul, checked_mul, usize);
#[cfg(has_i128)]
checked_impl!(CheckedMul, checked_mul, u128);

checked_impl!(CheckedMul, checked_mul, i8);
checked_impl!(CheckedMul, checked_mul, i16);
checked_impl!(CheckedMul, checked_mul, i32);
checked_impl!(CheckedMul, checked_mul, i64);
checked_impl!(CheckedMul, checked_mul, isize);
#[cfg(has_i128)]
checked_impl!(CheckedMul, checked_mul, i128);

/// Performs division that returns `None` instead of panicking on division by zero and instead of
/// wrapping around on underflow and overflow.
pub trait CheckedDiv: Sized + Div<Self, Output = Self> {
    /// Divides two numbers, checking for underflow, overflow and division by
    /// zero. If any of that happens, `None` is returned.
    fn checked_div(&self, v: &Self) -> Option<Self>;
}

checked_impl!(CheckedDiv, checked_div, u8);
checked_impl!(CheckedDiv, checked_div, u16);
checked_impl!(CheckedDiv, checked_div, u32);
checked_impl!(CheckedDiv, checked_div, u64);
checked_impl!(CheckedDiv, checked_div, usize);
#[cfg(has_i128)]
checked_impl!(CheckedDiv, checked_div, u128);

checked_impl!(CheckedDiv, checked_div, i8);
checked_impl!(CheckedDiv, checked_div, i16);
checked_impl!(CheckedDiv, checked_div, i32);
checked_impl!(CheckedDiv, checked_div, i64);
checked_impl!(CheckedDiv, checked_div, isize);
#[cfg(has_i128)]
checked_impl!(CheckedDiv, checked_div, i128);

/// Performs an integral remainder that returns `None` instead of panicking on division by zero and
/// instead of wrapping around on underflow and overflow.
pub trait CheckedRem: Sized + Rem<Self, Output = Self> {
    /// Finds the remainder of dividing two numbers, checking for underflow, overflow and division
    /// by zero. If any of that happens, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::CheckedRem;
    /// use std::i32::MIN;
    ///
    /// assert_eq!(CheckedRem::checked_rem(&10, &7), Some(3));
    /// assert_eq!(CheckedRem::checked_rem(&10, &-7), Some(3));
    /// assert_eq!(CheckedRem::checked_rem(&-10, &7), Some(-3));
    /// assert_eq!(CheckedRem::checked_rem(&-10, &-7), Some(-3));
    ///
    /// assert_eq!(CheckedRem::checked_rem(&10, &0), None);
    ///
    /// assert_eq!(CheckedRem::checked_rem(&MIN, &1), Some(0));
    /// assert_eq!(CheckedRem::checked_rem(&MIN, &-1), None);
    /// ```
    fn checked_rem(&self, v: &Self) -> Option<Self>;
}

checked_impl!(CheckedRem, checked_rem, u8);
checked_impl!(CheckedRem, checked_rem, u16);
checked_impl!(CheckedRem, checked_rem, u32);
checked_impl!(CheckedRem, checked_rem, u64);
checked_impl!(CheckedRem, checked_rem, usize);
#[cfg(has_i128)]
checked_impl!(CheckedRem, checked_rem, u128);

checked_impl!(CheckedRem, checked_rem, i8);
checked_impl!(CheckedRem, checked_rem, i16);
checked_impl!(CheckedRem, checked_rem, i32);
checked_impl!(CheckedRem, checked_rem, i64);
checked_impl!(CheckedRem, checked_rem, isize);
#[cfg(has_i128)]
checked_impl!(CheckedRem, checked_rem, i128);

macro_rules! checked_impl_unary {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self) -> Option<$t> {
                <$t>::$method(*self)
            }
        }
    };
}

/// Performs negation that returns `None` if the result can't be represented.
pub trait CheckedNeg: Sized {
    /// Negates a number, returning `None` for results that can't be represented, like signed `MIN`
    /// values that can't be positive, or non-zero unsigned values that can't be negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::CheckedNeg;
    /// use std::i32::MIN;
    ///
    /// assert_eq!(CheckedNeg::checked_neg(&1_i32), Some(-1));
    /// assert_eq!(CheckedNeg::checked_neg(&-1_i32), Some(1));
    /// assert_eq!(CheckedNeg::checked_neg(&MIN), None);
    ///
    /// assert_eq!(CheckedNeg::checked_neg(&0_u32), Some(0));
    /// assert_eq!(CheckedNeg::checked_neg(&1_u32), None);
    /// ```
    fn checked_neg(&self) -> Option<Self>;
}

checked_impl_unary!(CheckedNeg, checked_neg, u8);
checked_impl_unary!(CheckedNeg, checked_neg, u16);
checked_impl_unary!(CheckedNeg, checked_neg, u32);
checked_impl_unary!(CheckedNeg, checked_neg, u64);
checked_impl_unary!(CheckedNeg, checked_neg, usize);
#[cfg(has_i128)]
checked_impl_unary!(CheckedNeg, checked_neg, u128);

checked_impl_unary!(CheckedNeg, checked_neg, i8);
checked_impl_unary!(CheckedNeg, checked_neg, i16);
checked_impl_unary!(CheckedNeg, checked_neg, i32);
checked_impl_unary!(CheckedNeg, checked_neg, i64);
checked_impl_unary!(CheckedNeg, checked_neg, isize);
#[cfg(has_i128)]
checked_impl_unary!(CheckedNeg, checked_neg, i128);

/// Performs a left shift that returns `None` on shifts larger than
/// the type width.
pub trait CheckedShl: Sized + Shl<u32, Output = Self> {
    /// Checked shift left. Computes `self << rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    ///
    /// ```
    /// use num_traits::CheckedShl;
    ///
    /// let x: u16 = 0x0001;
    ///
    /// assert_eq!(CheckedShl::checked_shl(&x, 0),  Some(0x0001));
    /// assert_eq!(CheckedShl::checked_shl(&x, 1),  Some(0x0002));
    /// assert_eq!(CheckedShl::checked_shl(&x, 15), Some(0x8000));
    /// assert_eq!(CheckedShl::checked_shl(&x, 16), None);
    /// ```
    fn checked_shl(&self, rhs: u32) -> Option<Self>;
}

macro_rules! checked_shift_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, rhs: u32) -> Option<$t> {
                <$t>::$method(*self, rhs)
            }
        }
    };
}

checked_shift_impl!(CheckedShl, checked_shl, u8);
checked_shift_impl!(CheckedShl, checked_shl, u16);
checked_shift_impl!(CheckedShl, checked_shl, u32);
checked_shift_impl!(CheckedShl, checked_shl, u64);
checked_shift_impl!(CheckedShl, checked_shl, usize);
#[cfg(has_i128)]
checked_shift_impl!(CheckedShl, checked_shl, u128);

checked_shift_impl!(CheckedShl, checked_shl, i8);
checked_shift_impl!(CheckedShl, checked_shl, i16);
checked_shift_impl!(CheckedShl, checked_shl, i32);
checked_shift_impl!(CheckedShl, checked_shl, i64);
checked_shift_impl!(CheckedShl, checked_shl, isize);
#[cfg(has_i128)]
checked_shift_impl!(CheckedShl, checked_shl, i128);

/// Performs a right shift that returns `None` on shifts larger than
/// the type width.
pub trait CheckedShr: Sized + Shr<u32, Output = Self> {
    /// Checked shift right. Computes `self >> rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    ///
    /// ```
    /// use num_traits::CheckedShr;
    ///
    /// let x: u16 = 0x8000;
    ///
    /// assert_eq!(CheckedShr::checked_shr(&x, 0),  Some(0x8000));
    /// assert_eq!(CheckedShr::checked_shr(&x, 1),  Some(0x4000));
    /// assert_eq!(CheckedShr::checked_shr(&x, 15), Some(0x0001));
    /// assert_eq!(CheckedShr::checked_shr(&x, 16), None);
    /// ```
    fn checked_shr(&self, rhs: u32) -> Option<Self>;
}

checked_shift_impl!(CheckedShr, checked_shr, u8);
checked_shift_impl!(CheckedShr, checked_shr, u16);
checked_shift_impl!(CheckedShr, checked_shr, u32);
checked_shift_impl!(CheckedShr, checked_shr, u64);
checked_shift_impl!(CheckedShr, checked_shr, usize);
#[cfg(has_i128)]
checked_shift_impl!(CheckedShr, checked_shr, u128);

checked_shift_impl!(CheckedShr, checked_shr, i8);
checked_shift_impl!(CheckedShr, checked_shr, i16);
checked_shift_impl!(CheckedShr, checked_shr, i32);
checked_shift_impl!(CheckedShr, checked_shr, i64);
checked_shift_impl!(CheckedShr, checked_shr, isize);
#[cfg(has_i128)]
checked_shift_impl!(CheckedShr, checked_shr, i128);
#[cfg(test)]
mod tests_rug_1503 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 20;

        assert_eq!(<u8 as CheckedAdd>::checked_add(&p0, &p1), Some(30));
    }
}#[cfg(test)]
mod tests_rug_1504 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 300;
        let mut p1: u16 = 200;

        assert_eq!(<u16 as CheckedAdd>::checked_add(&p0, &p1), Some(500));
        assert_eq!(<u16 as CheckedAdd>::checked_add(&p0, &35000), None);
    }
}#[cfg(test)]
mod tests_rug_1505 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 20;

        assert_eq!(<u32 as CheckedAdd>::checked_add(&p0, &p1), Some(30));
    }
}#[cfg(test)]
mod tests_rug_1506 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615;
        let mut p1: u64 = 1;

        <u64 as CheckedAdd>::checked_add(&p0, &p1);

    }
}#[cfg(test)]
mod tests_rug_1507 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 20;

        <usize as CheckedAdd>::checked_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1508 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615;
        let mut p1: u128 = 1;

        assert_eq!(<u128 as CheckedAdd>::checked_add(&p0, &p1), None);
    }
}#[cfg(test)]
mod tests_rug_1509 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 20;

        let result = <i8 as CheckedAdd>::checked_add(&p0, &p1);

        assert_eq!(result, Some(30));
    }
}#[cfg(test)]
mod tests_rug_1510 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32760;
        let mut p1: i16 = 10;

        <i16 as CheckedAdd>::checked_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1511 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 20;

        <i32 as CheckedAdd>::checked_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1512 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;
        let mut p1: i64 = 67890;

        <i64 as CheckedAdd>::checked_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1513 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123;
        let mut p1: isize = 456;

        <isize as CheckedAdd>::checked_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1514 {
    use super::*;
    use crate::CheckedAdd;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807;
        let mut p1: i128 = 1;

        <i128 as CheckedAdd>::checked_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1515 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 3;

        assert_eq!(<u8 as CheckedSub>::checked_sub(&p0, &p1), Some(7));
        assert_eq!(<u8 as CheckedSub>::checked_sub(&p1, &p0), None);
    }
}#[cfg(test)]
mod tests_rug_1516 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 10;
        let mut p1: u16 = 5;

        assert_eq!(<u16 as CheckedSub>::checked_sub(&p0, &p1), Some(5));
        assert_eq!(<u16 as CheckedSub>::checked_sub(&p1, &p0), None);
    }
}#[cfg(test)]
mod tests_rug_1517 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 5;

        assert_eq!(<u32 as CheckedSub>::checked_sub(&p0, &p1), Some(5));
        assert_eq!(<u32 as CheckedSub>::checked_sub(&p1, &p0), None);
    }
}#[cfg(test)]
mod tests_rug_1518 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 10;
        let mut p1: u64 = 5;

        assert_eq!(<u64 as CheckedSub>::checked_sub(&p0, &p1), Some(5));
        assert_eq!(<u64 as CheckedSub>::checked_sub(&p1, &p0), None);
    }
}#[cfg(test)]
mod tests_rug_1519 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 5;

        <usize as CheckedSub>::checked_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1520 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615;
        let mut p1: u128 = 1;

        assert_eq!(<u128 as CheckedSub>::checked_sub(&p0, &p1), Some(18446744073709551614));
        assert_eq!(<u128 as CheckedSub>::checked_sub(&p1, &p0), None);
    }
}#[cfg(test)]
mod tests_rug_1521 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 5;

        <i8 as CheckedSub>::checked_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1522 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 10;
        let mut p1: i16 = 5;

        <i16 as CheckedSub>::checked_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1523 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 5;

        <i32 as CheckedSub>::checked_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1524 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: i64 = 5;

        <i64 as CheckedSub>::checked_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1525 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: isize = 10;
        let mut p1: isize = 5;

        <isize as CheckedSub>::checked_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1526 {
    use super::*;
    use crate::CheckedSub;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 10;
        let mut p1: i128 = 5;

        <i128 as CheckedSub>::checked_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1527 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 123;
        let mut p1: u8 = 45;

        <u8 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1528 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 123;
        let mut p1: u16 = 456;

        <u16 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1529 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 5;

        assert_eq!(<u32 as CheckedMul>::checked_mul(&p0, &p1), Some(50));
        assert_eq!(<u32 as CheckedMul>::checked_mul(&p0, &(u32::MAX / p0 + 1)), None);
    }
}#[cfg(test)]
mod tests_rug_1530 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;
        let mut p1: u64 = 67890;

        <u64 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1531 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 5;

        <usize as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1532 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;
        let mut p1: u128 = 98765432109876543210987654321098765432;

        <u128 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1533 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 12;
        let mut p1: i8 = 3;

        assert_eq!(<i8 as CheckedMul>::checked_mul(&p0, &p1), Some(36));
        assert_eq!(<i8 as CheckedMul>::checked_mul(&p0, &85), None); // Example of overflow
    }
}#[cfg(test)]
mod tests_rug_1534 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 123;
        let mut p1: i16 = 456;

        <i16 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1535 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 5;

        <i32 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1536 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;
        let mut p1: i64 = 987654321;

        <i64 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1537 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;
        let mut p1: isize = 67890;

        <isize as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1538 {
    use super::*;
    use crate::CheckedMul;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128
        let mut p1: i128 = 2;                  // Sample data for i128

        <i128 as CheckedMul>::checked_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1539 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 2;

        assert_eq!(<u8 as CheckedDiv>::checked_div(&p0, &p1), Some(5));
    }

    #[test]
    fn test_rug_div_by_zero() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 0;

        assert_eq!(<u8 as CheckedDiv>::checked_div(&p0, &p1), None);
    }
}#[cfg(test)]
mod tests_rug_1540 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 10;
        let mut p1: u16 = 2;

        <u16 as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1541 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 2;

        <u32 as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1542 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 100;
        let mut p1: u64 = 20;

        assert_eq!(<u64 as CheckedDiv>::checked_div(&p0, &p1), Some(5));
        
        // Test division by zero
        p1 = 0;
        assert_eq!(<u64 as CheckedDiv>::checked_div(&p0, &p1), None);
    }
}#[cfg(test)]
mod tests_rug_1543 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 2;

        <usize as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1544 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128
        let mut p1: u128 = 1; // Sample data for u128

        assert_eq!(<u128 as CheckedDiv>::checked_div(&p0, &p1), Some(p0));
        assert_eq!(<u128 as CheckedDiv>::checked_div(&p0, &0), None);
    }
}#[cfg(test)]
mod tests_rug_1545 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 2;

        <i8 as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1546 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 10;
        let mut p1: i16 = 2;

        <i16 as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1547 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 2;

        <i32 as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1548 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let p0: i64 = 10;
        let p1: i64 = 2;

        <i64 as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1549 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: isize = 6;

        <isize as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1550 {
    use super::*;
    use crate::CheckedDiv;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 100;
        let mut p1: i128 = 5;

        <i128 as CheckedDiv>::checked_div(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1551 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 3;

        <u8 as CheckedRem>::checked_rem(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1552 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 256;
        let mut p1: u16 = 3;

        <u16 as CheckedRem>::checked_rem(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1553 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 15;
        let mut p1: u32 = 4;

        <u32 as CheckedRem>::checked_rem(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1554 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;
        let mut p1: u64 = 6789;

        assert_eq!(<u64 as CheckedRem>::checked_rem(&p0, &p1), Some(12345 % 6789));
    }
}#[cfg(test)]
mod tests_rug_1555 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;
        let mut p1: usize = 5;

        <usize as CheckedRem>::checked_rem(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1556 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 123456789012345678901234567890123456789;
        let mut p1: u128 = 98765432109876543210987654321;

        assert_eq!(<u128 as CheckedRem>::checked_rem(&p0, &p1), Some(1234567890123456789));
    }
}#[cfg(test)]
mod tests_rug_1557 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 3;

        assert_eq!(<i8 as CheckedRem>::checked_rem(&p0, &p1), Some(1));
        
        // Test division by zero
        let p2: i8 = 0;
        assert_eq!(<i8 as CheckedRem>::checked_rem(&p0, &p2), None);
    }
}#[cfg(test)]
mod tests_rug_1558 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 10;
        let mut p1: i16 = 3;

        <i16 as CheckedRem>::checked_rem(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1559 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 15;
        let mut p1: i32 = 4;

        assert_eq!(<i32 as CheckedRem>::checked_rem(&p0, &p1), Some(3));
    }
}#[cfg(test)]
mod tests_rug_1560 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;
        let mut p1: i64 = 6789;

        assert_eq!(<i64 as CheckedRem>::checked_rem(&p0, &p1), Some(12345 % 6789));
    }
}#[cfg(test)]
mod tests_rug_1561 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: isize = 5;

        <isize as CheckedRem>::checked_rem(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1562 {
    use super::*;
    use crate::CheckedRem;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789;
        let mut p1: i128 = 98765432109876543210987654321;

        <i128 as CheckedRem>::checked_rem(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1563 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 123;

        assert_eq!(p0.checked_neg(), Some(133));
    }
}#[cfg(test)]
mod tests_rug_1564 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 500;

        assert_eq!(p0.checked_neg(), Some(65136)); // Since -500 in u16 is 65136
    }
}#[cfg(test)]
mod tests_rug_1565 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        assert_eq!(p0.checked_neg(), Some(4294967254));
    }
}#[cfg(test)]
mod tests_rug_1566 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64, which is u64::MAX

        assert_eq!(<u64 as CheckedNeg>::checked_neg(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_1567 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let p0: usize = 12345;

        <usize as CheckedNeg>::checked_neg(&p0);
    }
}#[cfg(test)]
mod tests_rug_1568 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        assert_eq!(p0.checked_neg(), Some(18446744073709551614));
    }
}#[cfg(test)]
mod tests_rug_1569 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;

        assert_eq!(p0.checked_neg(), Some(-127));
        assert_eq!((-128i8).checked_neg(), None);
    }
}#[cfg(test)]
mod tests_rug_1570 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Sample data for i16

        assert_eq!(p0.checked_neg(), Some(-32767));
        p0 = -32768;
        assert_eq!(p0.checked_neg(), None); // Overflow case
        p0 = 0;
        assert_eq!(p0.checked_neg(), Some(0));
    }
}#[cfg(test)]
mod tests_rug_1571 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        assert_eq!(p0.checked_neg(), Some(-42));
        
        p0 = -1;
        assert_eq!(p0.checked_neg(), Some(1));
        
        p0 = 0;
        assert_eq!(p0.checked_neg(), Some(0));

        // Test the edge case for overflow
        p0 = i32::MIN;
        assert_eq!(p0.checked_neg(), None);
    }
}#[cfg(test)]
mod tests_rug_1572 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let mut p0: i64 = -123;

        assert_eq!(p0.checked_neg(), Some(123));
        
        p0 = 123;
        assert_eq!(p0.checked_neg(), Some(-123));
        
        p0 = std::i64::MIN;
        assert_eq!(p0.checked_neg(), None);
    }
}#[cfg(test)]
mod tests_rug_1573 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let p0: isize = 123456789;

        assert_eq!(p0.checked_neg(), Some(-123456789));
        assert_eq!((-p0).checked_neg(), Some(123456789));
        assert_eq!(isize::MIN.checked_neg(), None);
    }
}#[cfg(test)]
mod tests_rug_1574 {
    use super::*;
    use crate::CheckedNeg;

    #[test]
    fn test_rug() {
        let p0: i128 = -9223372036854775808; // Sample data for i128

        assert_eq!((p0 as i128).checked_neg(), Some(9223372036854775808));
        
        let p1: i128 = 0;
        assert_eq!(p1.checked_neg(), Some(0));

        let p2: i128 = 1234567890123456789;
        assert_eq!(p2.checked_neg(), Some(-1234567890123456789));

        let p3: i128 = -1234567890123456789;
        assert_eq!(p3.checked_neg(), Some(1234567890123456789));
    }
}#[cfg(test)]
mod tests_rug_1575 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: u32 = 3;

        <u8 as CheckedShl>::checked_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1576 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: u32 = 3;

        <u16 as CheckedShl>::checked_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1577 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4; // Sample data for the first argument
        let mut p1: u32 = 2; // Sample data for the second argument

        assert_eq!(<u32 as CheckedShl>::checked_shl(&p0, p1), Some(16));
    }
}#[cfg(test)]
mod tests_rug_1578 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u32 = 32; // Sample data for u32

        <u64 as CheckedShl>::checked_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1579 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: usize = 4;
        let mut p1: u32 = 2;

        <usize as CheckedShl>::checked_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1580 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42;
        let mut p1: u32 = 5;

        <u128 as CheckedShl>::checked_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1581 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 5;
        let mut p1: u32 = 2;

        assert_eq!(<i8 as CheckedShl>::checked_shl(&p0, p1), Some(20));
    }
}#[cfg(test)]
mod tests_rug_1582 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 5;
        let mut p1: u32 = 3;

        assert_eq!(<i16 as CheckedShl>::checked_shl(&p0, p1), Some(40));
    }
}#[cfg(test)]
mod tests_rug_1583 {
    use super::*;
    use crate::ops::checked::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 1;
        let mut p1: u32 = 1;

        <i32 as CheckedShl>::checked_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1584 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: u32 = 3;

        assert_eq!(<i64 as CheckedShl>::checked_shl(&p0, p1), Some(80));
    }
}#[cfg(test)]
mod tests_rug_1585 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: isize = 16;
        let mut p1: u32 = 3;

        <isize as CheckedShl>::checked_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1586 {
    use super::*;
    use crate::CheckedShl;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: u32 = 5;

        assert_eq!(<i128 as CheckedShl>::checked_shl(&p0, p1), Some(1344));
    }
}#[cfg(test)]
mod tests_rug_1587 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 16;
        let mut p1: u32 = 2;

        assert_eq!(p0.checked_shr(p1), Some(4));
    }
}#[cfg(test)]
mod tests_rug_1588 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;
        let mut p1: u32 = 3;

        assert_eq!(p0.checked_shr(p1), Some(5));
    }
}#[cfg(test)]
mod tests_rug_1589 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;
        let mut p1: u32 = 3;

        assert_eq!(<u32 as CheckedShr>::checked_shr(&p0, p1), Some(5));
    }
}#[cfg(test)]
mod tests_rug_1590 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 42;
        let mut p1: u32 = 3;

        <u64 as CheckedShr>::checked_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1591 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: usize = 16;
        let mut p1: u32 = 2;

        <usize as CheckedShr>::checked_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1592 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Example sample data for u128
        let mut p1: u32 = 4; // Example sample data for u32

        <u128 as CheckedShr>::checked_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1593 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 16;
        let mut p1: u32 = 2;

        <i8 as CheckedShr>::checked_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1594 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;
        let mut p1: u32 = 3;

        <i16 as CheckedShr>::checked_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1595 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 16;
        let mut p1: u32 = 2;

        assert_eq!(<i32 as CheckedShr>::checked_shr(&p0, p1), Some(4));
    }
}#[cfg(test)]
mod tests_rug_1596 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 16;
        let mut p1: u32 = 2;

        <i64 as CheckedShr>::checked_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1597 {
    use super::*;
    use crate::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: isize = 16;
        let mut p1: u32 = 2;

        assert_eq!(<isize as CheckedShr>::checked_shr(&p0, p1), Some(4));
    }
}#[cfg(test)]
mod tests_rug_1598 {
    use super::*;
    use crate::ops::checked::CheckedShr;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456;
        let mut p1: u32 = 10;

        assert_eq!(p0.checked_shr(p1), Some(123456789012345678901234567890));
    }
}