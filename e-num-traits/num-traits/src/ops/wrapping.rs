use core::num::Wrapping;
use core::ops::{Add, Mul, Neg, Shl, Shr, Sub};

macro_rules! wrapping_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &Self) -> Self {
                <$t>::$method(*self, *v)
            }
        }
    };
    ($trait_name:ident, $method:ident, $t:ty, $rhs:ty) => {
        impl $trait_name<$rhs> for $t {
            #[inline]
            fn $method(&self, v: &$rhs) -> Self {
                <$t>::$method(*self, *v)
            }
        }
    };
}

/// Performs addition that wraps around on overflow.
pub trait WrappingAdd: Sized + Add<Self, Output = Self> {
    /// Wrapping (modular) addition. Computes `self + other`, wrapping around at the boundary of
    /// the type.
    fn wrapping_add(&self, v: &Self) -> Self;
}

wrapping_impl!(WrappingAdd, wrapping_add, u8);
wrapping_impl!(WrappingAdd, wrapping_add, u16);
wrapping_impl!(WrappingAdd, wrapping_add, u32);
wrapping_impl!(WrappingAdd, wrapping_add, u64);
wrapping_impl!(WrappingAdd, wrapping_add, usize);
#[cfg(has_i128)]
wrapping_impl!(WrappingAdd, wrapping_add, u128);

wrapping_impl!(WrappingAdd, wrapping_add, i8);
wrapping_impl!(WrappingAdd, wrapping_add, i16);
wrapping_impl!(WrappingAdd, wrapping_add, i32);
wrapping_impl!(WrappingAdd, wrapping_add, i64);
wrapping_impl!(WrappingAdd, wrapping_add, isize);
#[cfg(has_i128)]
wrapping_impl!(WrappingAdd, wrapping_add, i128);

/// Performs subtraction that wraps around on overflow.
pub trait WrappingSub: Sized + Sub<Self, Output = Self> {
    /// Wrapping (modular) subtraction. Computes `self - other`, wrapping around at the boundary
    /// of the type.
    fn wrapping_sub(&self, v: &Self) -> Self;
}

wrapping_impl!(WrappingSub, wrapping_sub, u8);
wrapping_impl!(WrappingSub, wrapping_sub, u16);
wrapping_impl!(WrappingSub, wrapping_sub, u32);
wrapping_impl!(WrappingSub, wrapping_sub, u64);
wrapping_impl!(WrappingSub, wrapping_sub, usize);
#[cfg(has_i128)]
wrapping_impl!(WrappingSub, wrapping_sub, u128);

wrapping_impl!(WrappingSub, wrapping_sub, i8);
wrapping_impl!(WrappingSub, wrapping_sub, i16);
wrapping_impl!(WrappingSub, wrapping_sub, i32);
wrapping_impl!(WrappingSub, wrapping_sub, i64);
wrapping_impl!(WrappingSub, wrapping_sub, isize);
#[cfg(has_i128)]
wrapping_impl!(WrappingSub, wrapping_sub, i128);

/// Performs multiplication that wraps around on overflow.
pub trait WrappingMul: Sized + Mul<Self, Output = Self> {
    /// Wrapping (modular) multiplication. Computes `self * other`, wrapping around at the boundary
    /// of the type.
    fn wrapping_mul(&self, v: &Self) -> Self;
}

wrapping_impl!(WrappingMul, wrapping_mul, u8);
wrapping_impl!(WrappingMul, wrapping_mul, u16);
wrapping_impl!(WrappingMul, wrapping_mul, u32);
wrapping_impl!(WrappingMul, wrapping_mul, u64);
wrapping_impl!(WrappingMul, wrapping_mul, usize);
#[cfg(has_i128)]
wrapping_impl!(WrappingMul, wrapping_mul, u128);

wrapping_impl!(WrappingMul, wrapping_mul, i8);
wrapping_impl!(WrappingMul, wrapping_mul, i16);
wrapping_impl!(WrappingMul, wrapping_mul, i32);
wrapping_impl!(WrappingMul, wrapping_mul, i64);
wrapping_impl!(WrappingMul, wrapping_mul, isize);
#[cfg(has_i128)]
wrapping_impl!(WrappingMul, wrapping_mul, i128);

macro_rules! wrapping_unary_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self) -> $t {
                <$t>::$method(*self)
            }
        }
    };
}

/// Performs a negation that does not panic.
pub trait WrappingNeg: Sized {
    /// Wrapping (modular) negation. Computes `-self`,
    /// wrapping around at the boundary of the type.
    ///
    /// Since unsigned types do not have negative equivalents
    /// all applications of this function will wrap (except for `-0`).
    /// For values smaller than the corresponding signed type's maximum
    /// the result is the same as casting the corresponding signed value.
    /// Any larger values are equivalent to `MAX + 1 - (val - MAX - 1)` where
    /// `MAX` is the corresponding signed type's maximum.
    ///
    /// ```
    /// use num_traits::WrappingNeg;
    ///
    /// assert_eq!(100i8.wrapping_neg(), -100);
    /// assert_eq!((-100i8).wrapping_neg(), 100);
    /// assert_eq!((-128i8).wrapping_neg(), -128); // wrapped!
    /// ```
    fn wrapping_neg(&self) -> Self;
}

wrapping_unary_impl!(WrappingNeg, wrapping_neg, u8);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, u16);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, u32);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, u64);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, usize);
#[cfg(has_i128)]
wrapping_unary_impl!(WrappingNeg, wrapping_neg, u128);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, i8);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, i16);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, i32);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, i64);
wrapping_unary_impl!(WrappingNeg, wrapping_neg, isize);
#[cfg(has_i128)]
wrapping_unary_impl!(WrappingNeg, wrapping_neg, i128);

macro_rules! wrapping_shift_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, rhs: u32) -> $t {
                <$t>::$method(*self, rhs)
            }
        }
    };
}

/// Performs a left shift that does not panic.
pub trait WrappingShl: Sized + Shl<usize, Output = Self> {
    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
    /// where `mask` removes any high order bits of `rhs` that would
    /// cause the shift to exceed the bitwidth of the type.
    ///
    /// ```
    /// use num_traits::WrappingShl;
    ///
    /// let x: u16 = 0x0001;
    ///
    /// assert_eq!(WrappingShl::wrapping_shl(&x, 0),  0x0001);
    /// assert_eq!(WrappingShl::wrapping_shl(&x, 1),  0x0002);
    /// assert_eq!(WrappingShl::wrapping_shl(&x, 15), 0x8000);
    /// assert_eq!(WrappingShl::wrapping_shl(&x, 16), 0x0001);
    /// ```
    fn wrapping_shl(&self, rhs: u32) -> Self;
}

wrapping_shift_impl!(WrappingShl, wrapping_shl, u8);
wrapping_shift_impl!(WrappingShl, wrapping_shl, u16);
wrapping_shift_impl!(WrappingShl, wrapping_shl, u32);
wrapping_shift_impl!(WrappingShl, wrapping_shl, u64);
wrapping_shift_impl!(WrappingShl, wrapping_shl, usize);
#[cfg(has_i128)]
wrapping_shift_impl!(WrappingShl, wrapping_shl, u128);

wrapping_shift_impl!(WrappingShl, wrapping_shl, i8);
wrapping_shift_impl!(WrappingShl, wrapping_shl, i16);
wrapping_shift_impl!(WrappingShl, wrapping_shl, i32);
wrapping_shift_impl!(WrappingShl, wrapping_shl, i64);
wrapping_shift_impl!(WrappingShl, wrapping_shl, isize);
#[cfg(has_i128)]
wrapping_shift_impl!(WrappingShl, wrapping_shl, i128);

/// Performs a right shift that does not panic.
pub trait WrappingShr: Sized + Shr<usize, Output = Self> {
    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
    /// where `mask` removes any high order bits of `rhs` that would
    /// cause the shift to exceed the bitwidth of the type.
    ///
    /// ```
    /// use num_traits::WrappingShr;
    ///
    /// let x: u16 = 0x8000;
    ///
    /// assert_eq!(WrappingShr::wrapping_shr(&x, 0),  0x8000);
    /// assert_eq!(WrappingShr::wrapping_shr(&x, 1),  0x4000);
    /// assert_eq!(WrappingShr::wrapping_shr(&x, 15), 0x0001);
    /// assert_eq!(WrappingShr::wrapping_shr(&x, 16), 0x8000);
    /// ```
    fn wrapping_shr(&self, rhs: u32) -> Self;
}

wrapping_shift_impl!(WrappingShr, wrapping_shr, u8);
wrapping_shift_impl!(WrappingShr, wrapping_shr, u16);
wrapping_shift_impl!(WrappingShr, wrapping_shr, u32);
wrapping_shift_impl!(WrappingShr, wrapping_shr, u64);
wrapping_shift_impl!(WrappingShr, wrapping_shr, usize);
#[cfg(has_i128)]
wrapping_shift_impl!(WrappingShr, wrapping_shr, u128);

wrapping_shift_impl!(WrappingShr, wrapping_shr, i8);
wrapping_shift_impl!(WrappingShr, wrapping_shr, i16);
wrapping_shift_impl!(WrappingShr, wrapping_shr, i32);
wrapping_shift_impl!(WrappingShr, wrapping_shr, i64);
wrapping_shift_impl!(WrappingShr, wrapping_shr, isize);
#[cfg(has_i128)]
wrapping_shift_impl!(WrappingShr, wrapping_shr, i128);

// Well this is a bit funny, but all the more appropriate.
impl<T: WrappingAdd> WrappingAdd for Wrapping<T>
where
    Wrapping<T>: Add<Output = Wrapping<T>>,
{
    fn wrapping_add(&self, v: &Self) -> Self {
        Wrapping(self.0.wrapping_add(&v.0))
    }
}
impl<T: WrappingSub> WrappingSub for Wrapping<T>
where
    Wrapping<T>: Sub<Output = Wrapping<T>>,
{
    fn wrapping_sub(&self, v: &Self) -> Self {
        Wrapping(self.0.wrapping_sub(&v.0))
    }
}
impl<T: WrappingMul> WrappingMul for Wrapping<T>
where
    Wrapping<T>: Mul<Output = Wrapping<T>>,
{
    fn wrapping_mul(&self, v: &Self) -> Self {
        Wrapping(self.0.wrapping_mul(&v.0))
    }
}
impl<T: WrappingNeg> WrappingNeg for Wrapping<T>
where
    Wrapping<T>: Neg<Output = Wrapping<T>>,
{
    fn wrapping_neg(&self) -> Self {
        Wrapping(self.0.wrapping_neg())
    }
}
impl<T: WrappingShl> WrappingShl for Wrapping<T>
where
    Wrapping<T>: Shl<usize, Output = Wrapping<T>>,
{
    fn wrapping_shl(&self, rhs: u32) -> Self {
        Wrapping(self.0.wrapping_shl(rhs))
    }
}
impl<T: WrappingShr> WrappingShr for Wrapping<T>
where
    Wrapping<T>: Shr<usize, Output = Wrapping<T>>,
{
    fn wrapping_shr(&self, rhs: u32) -> Self {
        Wrapping(self.0.wrapping_shr(rhs))
    }
}

#[test]
fn test_wrapping_traits() {
    fn wrapping_add<T: WrappingAdd>(a: T, b: T) -> T {
        a.wrapping_add(&b)
    }
    fn wrapping_sub<T: WrappingSub>(a: T, b: T) -> T {
        a.wrapping_sub(&b)
    }
    fn wrapping_mul<T: WrappingMul>(a: T, b: T) -> T {
        a.wrapping_mul(&b)
    }
    fn wrapping_neg<T: WrappingNeg>(a: T) -> T {
        a.wrapping_neg()
    }
    fn wrapping_shl<T: WrappingShl>(a: T, b: u32) -> T {
        a.wrapping_shl(b)
    }
    fn wrapping_shr<T: WrappingShr>(a: T, b: u32) -> T {
        a.wrapping_shr(b)
    }
    assert_eq!(wrapping_add(255, 1), 0u8);
    assert_eq!(wrapping_sub(0, 1), 255u8);
    assert_eq!(wrapping_mul(255, 2), 254u8);
    assert_eq!(wrapping_neg(255), 1u8);
    assert_eq!(wrapping_shl(255, 8), 255u8);
    assert_eq!(wrapping_shr(255, 8), 255u8);
    assert_eq!(wrapping_add(255, 1), (Wrapping(255u8) + Wrapping(1u8)).0);
    assert_eq!(wrapping_sub(0, 1), (Wrapping(0u8) - Wrapping(1u8)).0);
    assert_eq!(wrapping_mul(255, 2), (Wrapping(255u8) * Wrapping(2u8)).0);
    // TODO: Test for Wrapping::Neg. Not possible yet since core::ops::Neg was
    // only added to core::num::Wrapping<_> in Rust 1.10.
    assert_eq!(wrapping_shl(255, 8), (Wrapping(255u8) << 8).0);
    assert_eq!(wrapping_shr(255, 8), (Wrapping(255u8) >> 8).0);
}

#[test]
fn wrapping_is_wrappingadd() {
    fn require_wrappingadd<T: WrappingAdd>(_: &T) {}
    require_wrappingadd(&Wrapping(42));
}

#[test]
fn wrapping_is_wrappingsub() {
    fn require_wrappingsub<T: WrappingSub>(_: &T) {}
    require_wrappingsub(&Wrapping(42));
}

#[test]
fn wrapping_is_wrappingmul() {
    fn require_wrappingmul<T: WrappingMul>(_: &T) {}
    require_wrappingmul(&Wrapping(42));
}

// TODO: Test for Wrapping::Neg. Not possible yet since core::ops::Neg was
// only added to core::num::Wrapping<_> in Rust 1.10.

#[test]
fn wrapping_is_wrappingshl() {
    fn require_wrappingshl<T: WrappingShl>(_: &T) {}
    require_wrappingshl(&Wrapping(42));
}

#[test]
fn wrapping_is_wrappingshr() {
    fn require_wrappingshr<T: WrappingShr>(_: &T) {}
    require_wrappingshr(&Wrapping(42));
}
#[cfg(test)]
mod tests_rug_1779 {
    use super::*;
    use crate::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 254;
        let mut p1: u8 = 3;

        let result = <u8 as WrappingAdd>::wrapping_add(&p0, &p1);

        assert_eq!(result, 1);
    }
}#[cfg(test)]
mod tests_rug_1780 {
    use super::*;
    use crate::ops::wrapping::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 65530;
        let mut p1: u16 = 10;

        let result = <u16 as WrappingAdd>::wrapping_add(&p0, &p1);
        assert_eq!(result, 4); // 65530 + 10 wraps around to 4 in u16
    }
}#[cfg(test)]
mod tests_rug_1781 {
    use super::*;
    use crate::ops::wrapping::WrappingAdd;

    #[test]
    fn test_wrapping_add() {
        let mut p0: u32 = 4294967295; // Sample data for u32, which is the maximum value
        let mut p1: u32 = 1;          // Sample data for u32

        let result = <u32 as WrappingAdd>::wrapping_add(&p0, &p1);
        
        assert_eq!(result, 0); // Since wrapping addition of max u32 and 1 should wrap around to 0
    }
}#[cfg(test)]
mod tests_rug_1782 {
    use super::*;
    use crate::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u64 = 1;                   // Sample data for u64

        let result = <u64 as WrappingAdd>::wrapping_add(&p0, &p1);
        assert_eq!(result, 0);
    }
}#[cfg(test)]
mod tests_rug_1783 {
    use super::*;
    use crate::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: usize = 18446744073709551615;
        let mut p1: usize = 1;

        let result = <usize as WrappingAdd>::wrapping_add(&p0, &p1);

        assert_eq!(result, 0);
    }
}#[cfg(test)]
mod tests_rug_1784 {
    use super::*;
    use crate::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128
        let mut p1: u128 = 1;                  // Sample data for u128

        <u128 as WrappingAdd>::wrapping_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1785 {
    use super::*;
    use crate::ops::wrapping::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;
        let mut p1: i8 = 1;

        <i8 as WrappingAdd>::wrapping_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1786 {
    use super::*;
    use crate::ops::wrapping::WrappingAdd;

    #[test]
    fn test_wrapping_add() {
        let mut p0: i16 = 32767;
        let mut p1: i16 = 1;

        let result = <i16 as WrappingAdd>::wrapping_add(&p0, &p1);
        assert_eq!(result, -32768);
    }
}#[cfg(test)]
mod tests_rug_1787 {
    use super::*;
    use crate::ops::wrapping::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2147483647;
        let mut p1: i32 = 1;

        let result = <i32 as WrappingAdd>::wrapping_add(&p0, &p1);
        assert_eq!(result, -2147483648);
    }
}#[cfg(test)]
mod tests_rug_1788 {
    use super::*;
    use crate::ops::wrapping::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 9223372036854775807; // Sample data for i64
        let mut p1: i64 = 1;                  // Sample data for i64

        <i64 as WrappingAdd>::wrapping_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1789 {
    use super::*;
    use crate::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123;
        let mut p1: isize = -456;

        <isize as WrappingAdd>::wrapping_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1790 {
    use super::*;
    use crate::WrappingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128
        let mut p1: i128 = 1;                  // Sample data for i128

        <i128 as WrappingAdd>::wrapping_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1791 {
    use super::*;
    use crate::ops::wrapping::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 20;

        <u8 as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1792 {
    use super::*;
    use crate::ops::wrapping::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: u16 = 3;

        <u16 as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1793 {
    use super::*;
    use crate::ops::wrapping::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 20;

        let result = <u32 as WrappingSub>::wrapping_sub(&p0, &p1);
        assert_eq!(result, 4294967286); // 10 - 20 wraps around in u32
    }
}#[cfg(test)]
mod tests_rug_1794 {
    use super::*;
    use crate::ops::wrapping::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 10;
        let mut p1: u64 = 20;

        <u64 as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1795 {
    use super::*;
    use crate::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 3;

        <usize as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1796 {
    use super::*;
    use crate::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 456;
        let mut p1: u128 = 123;

        <u128 as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1797 {
    use super::*;
    use crate::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;
        let mut p1: i8 = -1;

        <i8 as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1798 {
    use super::*;
    use crate::ops::wrapping::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 10;
        let mut p1: i16 = 20;

        let result = <i16 as WrappingSub>::wrapping_sub(&p0, &p1);
        assert_eq!(result, -10_i16);
    }
}#[cfg(test)]
mod tests_rug_1799 {
    use super::*;
    use crate::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 5;

        <i32 as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1800 {
    use super::*;
    use crate::ops::wrapping::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: i64 = 20;

        <i64 as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1801 {
    use super::*;
    use crate::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: isize = 10;
        let mut p1: isize = 20;

        <isize as WrappingSub>::wrapping_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1802 {
    use super::*;
    use crate::ops::wrapping::WrappingSub;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 10;
        let mut p1: i128 = 3;

        let result = <i128 as WrappingSub>::wrapping_sub(&p0, &p1);
        assert_eq!(result, 7);
    }
}#[cfg(test)]
mod tests_rug_1803 {
    use super::*;
    use crate::ops::wrapping::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 254;
        let mut p1: u8 = 3;

        let result = <u8 as WrappingMul>::wrapping_mul(&p0, &p1);
        assert_eq!(result, 6); // 254 * 3 = 762 which overflows and wraps around to 6 for u8
    }
}#[cfg(test)]
mod tests_rug_1804 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 500;
        let mut p1: u16 = 300;

        let result = <u16 as WrappingMul>::wrapping_mul(&p0, &p1);
        assert_eq!(result, 14208); // 500 * 300 % 2^16
    }
}#[cfg(test)]
mod tests_rug_1805 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 4294967295; // This is a sample value close to the max u32, which will cause wrapping.

        let result = <u32 as WrappingMul>::wrapping_mul(&p0, &p1);
        assert_eq!(result, 4294967285); // Expected result after wrapping multiplication
    }
}#[cfg(test)]
mod tests_rug_1806 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_wrapping_mul() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64, which is u64::MAX
        let mut p1: u64 = 2; // Another sample data for u64

        let result = <u64 as WrappingMul>::wrapping_mul(&p0, &p1);
        assert_eq!(result, 1); // Since (u64::MAX) * 2 wraps around to 1
    }
}#[cfg(test)]
mod tests_rug_1807 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 20;

        <usize as WrappingMul>::wrapping_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1808 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128
        let mut p1: u128 = 2;

        <u128 as WrappingMul>::wrapping_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1809 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;
        let mut p1: i8 = 2;

        <i8 as WrappingMul>::wrapping_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1810 {
    use super::*;
    use crate::ops::wrapping::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767;
        let mut p1: i16 = 2;

        let result = <i16 as WrappingMul>::wrapping_mul(&p0, &p1);
        assert_eq!(result, -2); // Expected result of wrapping multiplication
    }
}#[cfg(test)]
mod tests_rug_1811 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 1_000_000;
        let mut p1: i32 = 10;

        <i32 as WrappingMul>::wrapping_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1812 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 9223372036854775807; // Sample data for i64
        let mut p1: i64 = 2; // Sample data for i64

        <i64 as WrappingMul>::wrapping_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1813 {
    use super::*;
    use crate::WrappingMul;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;
        let mut p1: isize = -6789;

        <isize as WrappingMul>::wrapping_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1814 {
    use super::*;
    use crate::ops::wrapping::WrappingMul;

    #[test]
    fn test_wrapping_mul() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128
        let mut p1: i128 = 2; // Sample data for i128

        let result = <i128 as WrappingMul>::wrapping_mul(&p0, &p1);
        assert_eq!(result, -2);
    }
}#[cfg(test)]
mod tests_rug_1815 {
    use super::*;
    use crate::ops::wrapping::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5u8;

        p0.wrapping_neg();
    }
}#[cfg(test)]
mod tests_rug_1816 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 50000;

        let result = <u16 as WrappingNeg>::wrapping_neg(&p0);
        assert_eq!(result, 15696);
    }
}#[cfg(test)]
mod tests_rug_1817 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        let result = p0.wrapping_neg();
        assert_eq!(result, !p0 + 1);
    }
}#[cfg(test)]
mod tests_rug_1818 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_wrapping_neg() {
        let mut p0: u64 = 123456789;

        let result = <u64 as WrappingNeg>::wrapping_neg(&p0);
        assert_eq!(result, !p0 + 1);
    }
}#[cfg(test)]
mod tests_rug_1819 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;

        let result = <usize as WrappingNeg>::wrapping_neg(&p0);
        assert_eq!(result, std::usize::MAX - p0 + 1);
    }
}#[cfg(test)]
mod tests_rug_1820 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128

        p0.wrapping_neg();
    }
}#[cfg(test)]
mod tests_rug_1821 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;

        let result = p0.wrapping_neg();

        assert_eq!(result, -127);
    }
}#[cfg(test)]
mod tests_rug_1822 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Sample data for i16

        p0.wrapping_neg();
    }
}#[cfg(test)]
mod tests_rug_1823 {
    use super::*;
    use crate::ops::wrapping::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;

        let result = (<i32 as WrappingNeg>::wrapping_neg)(&p0);

        assert_eq!(result, -10);
    }
}#[cfg(test)]
mod tests_rug_1824 {
    use super::*;
    use crate::ops::wrapping::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        <i64 as WrappingNeg>::wrapping_neg(&p0);
    }
}#[cfg(test)]
mod tests_rug_1825 {
    use super::*;
    use crate::ops::wrapping::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: isize = -12345;

        assert_eq!(p0.wrapping_neg(), 12345);
    }
}#[cfg(test)]
mod tests_rug_1826 {
    use super::*;
    use crate::WrappingNeg;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 45678901234567890123456789012345_i128;

        <i128 as WrappingNeg>::wrapping_neg(&p0);
    }
}#[cfg(test)]
mod tests_rug_1827 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 15;
        let mut p1: u32 = 4;

        let result = <u8 as WrappingShl>::wrapping_shl(&p0, p1);
        assert_eq!(result, 240);
    }
}#[cfg(test)]
mod tests_rug_1828 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 15;
        let mut p1: u32 = 2;

        <u16 as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1829 {
    use super::*;
    use crate::ops::wrapping::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;
        let mut p1: u32 = 5;

        <u32 as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1830 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u32 = 32; // Sample data for u32

        <u64 as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1831 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;
        let mut p1: u32 = 5;

        <usize>::wrapping_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1832 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;
        let mut p1: u32 = 5u32;

        <u128 as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1833 {
    use super::*;
    use crate::ops::wrapping::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 1;
        let mut p1: u32 = 5;

        <i8 as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1834 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 15;
        let mut p1: u32 = 2;

        <i16 as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1835 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 16;
        let mut p1: u32 = 3;

        let result = <i32 as WrappingShl>::wrapping_shl(&p0, p1);
        assert_eq!(result, 128);
    }
}#[cfg(test)]
mod tests_rug_1836 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: u32 = 3;

        <i64 as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1837 {
    use super::*;
    use crate::ops::wrapping::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: u32 = 5;

        <isize as WrappingShl>::wrapping_shl(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1838 {
    use super::*;
    use crate::WrappingShl;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: u32 = 5;

        p0.wrapping_shl(p1);
    }
}#[cfg(test)]
mod tests_rug_1839 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 16;
        let mut p1: u32 = 2;

        let result = <u8 as WrappingShr>::wrapping_shr(&p0, p1);
        assert_eq!(result, 4);
    }
}#[cfg(test)]
mod tests_rug_1840 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;
        let mut p1: u32 = 3;

        let result = p0.wrapping_shr(p1);
        assert_eq!(result, 5); // 42 >> 3 == 5
    }
}#[cfg(test)]
mod tests_rug_1841 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;
        let mut p1: u32 = 5;

        <u32 as WrappingShr>::wrapping_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1842 {
    use super::*;
    use crate::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u32 = 32; // Sample data for u32

        <u64 as WrappingShr>::wrapping_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1843 {
    use super::*;
    use crate::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: usize = 18;
        let mut p1: u32 = 3;

        <usize>::wrapping_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1844 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128
        let mut p1: u32 = 10; // Sample data for u32

        <u128 as WrappingShr>::wrapping_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1845 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -123;
        let mut p1: u32 = 5;

        <i8 as WrappingShr>::wrapping_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1846 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 16;
        let mut p1: u32 = 2;

        <i16 as WrappingShr>::wrapping_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1847 {
    use super::*;
    use crate::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: i32 = -1;
        let mut p1: u32 = 1;

        let result = <i32 as WrappingShr>::wrapping_shr(&p0, p1);
        assert_eq!(result, -1); // Expected result for wrapping right shift of -1 by 1
    }
}#[cfg(test)]
mod tests_rug_1848 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_wrapping_shr() {
        let mut p0: i64 = 12345;
        let mut p1: u32 = 3;

        let result = <i64 as WrappingShr>::wrapping_shr(&p0, p1);
        assert_eq!(result, 1543); // Expected result of 12345 wrapping right shifted by 3
    }
}#[cfg(test)]
mod tests_rug_1849 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: isize = 16;
        let mut p1: u32 = 3;

        <isize as WrappingShr>::wrapping_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1850 {
    use super::*;
    use crate::ops::wrapping::WrappingShr;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: u32 = 3;

        <i128 as WrappingShr>::wrapping_shr(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1854 {
    use super::*;
    use crate::WrappingNeg;
    use crate::{One, Zero};
    use core::num::Wrapping;

    #[test]
    fn test_wrapping_neg() {
        let mut p0: Wrapping<i64> = Wrapping(i64::one()); // create the local variable p0 with type Wrapping<i64> using one()

        let result = p0.wrapping_neg();
        assert_eq!(result, Wrapping(-1));
    }
}#[cfg(test)]
mod tests_rug_1855 {
    use super::*;
    use crate::ops::wrapping::WrappingShl;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(15);
        let mut p1: u32 = 2;

        <core::num::Wrapping<i32> as WrappingShl>::wrapping_shl(&p0, p1);
    }
}