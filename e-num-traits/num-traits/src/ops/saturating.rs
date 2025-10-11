use core::ops::{Add, Mul, Sub};

/// Saturating math operations. Deprecated, use `SaturatingAdd`, `SaturatingSub` and
/// `SaturatingMul` instead.
pub trait Saturating {
    /// Saturating addition operator.
    /// Returns a+b, saturating at the numeric bounds instead of overflowing.
    fn saturating_add(self, v: Self) -> Self;

    /// Saturating subtraction operator.
    /// Returns a-b, saturating at the numeric bounds instead of overflowing.
    fn saturating_sub(self, v: Self) -> Self;
}

macro_rules! deprecated_saturating_impl {
    ($trait_name:ident for $($t:ty)*) => {$(
        impl $trait_name for $t {
            #[inline]
            fn saturating_add(self, v: Self) -> Self {
                Self::saturating_add(self, v)
            }

            #[inline]
            fn saturating_sub(self, v: Self) -> Self {
                Self::saturating_sub(self, v)
            }
        }
    )*}
}

deprecated_saturating_impl!(Saturating for isize usize i8 u8 i16 u16 i32 u32 i64 u64);
#[cfg(has_i128)]
deprecated_saturating_impl!(Saturating for i128 u128);

macro_rules! saturating_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &Self) -> Self {
                <$t>::$method(*self, *v)
            }
        }
    };
}

/// Performs addition that saturates at the numeric bounds instead of overflowing.
pub trait SaturatingAdd: Sized + Add<Self, Output = Self> {
    /// Saturating addition. Computes `self + other`, saturating at the relevant high or low boundary of
    /// the type.
    fn saturating_add(&self, v: &Self) -> Self;
}

saturating_impl!(SaturatingAdd, saturating_add, u8);
saturating_impl!(SaturatingAdd, saturating_add, u16);
saturating_impl!(SaturatingAdd, saturating_add, u32);
saturating_impl!(SaturatingAdd, saturating_add, u64);
saturating_impl!(SaturatingAdd, saturating_add, usize);
#[cfg(has_i128)]
saturating_impl!(SaturatingAdd, saturating_add, u128);

saturating_impl!(SaturatingAdd, saturating_add, i8);
saturating_impl!(SaturatingAdd, saturating_add, i16);
saturating_impl!(SaturatingAdd, saturating_add, i32);
saturating_impl!(SaturatingAdd, saturating_add, i64);
saturating_impl!(SaturatingAdd, saturating_add, isize);
#[cfg(has_i128)]
saturating_impl!(SaturatingAdd, saturating_add, i128);

/// Performs subtraction that saturates at the numeric bounds instead of overflowing.
pub trait SaturatingSub: Sized + Sub<Self, Output = Self> {
    /// Saturating subtraction. Computes `self - other`, saturating at the relevant high or low boundary of
    /// the type.
    fn saturating_sub(&self, v: &Self) -> Self;
}

saturating_impl!(SaturatingSub, saturating_sub, u8);
saturating_impl!(SaturatingSub, saturating_sub, u16);
saturating_impl!(SaturatingSub, saturating_sub, u32);
saturating_impl!(SaturatingSub, saturating_sub, u64);
saturating_impl!(SaturatingSub, saturating_sub, usize);
#[cfg(has_i128)]
saturating_impl!(SaturatingSub, saturating_sub, u128);

saturating_impl!(SaturatingSub, saturating_sub, i8);
saturating_impl!(SaturatingSub, saturating_sub, i16);
saturating_impl!(SaturatingSub, saturating_sub, i32);
saturating_impl!(SaturatingSub, saturating_sub, i64);
saturating_impl!(SaturatingSub, saturating_sub, isize);
#[cfg(has_i128)]
saturating_impl!(SaturatingSub, saturating_sub, i128);

/// Performs multiplication that saturates at the numeric bounds instead of overflowing.
pub trait SaturatingMul: Sized + Mul<Self, Output = Self> {
    /// Saturating multiplication. Computes `self * other`, saturating at the relevant high or low boundary of
    /// the type.
    fn saturating_mul(&self, v: &Self) -> Self;
}

saturating_impl!(SaturatingMul, saturating_mul, u8);
saturating_impl!(SaturatingMul, saturating_mul, u16);
saturating_impl!(SaturatingMul, saturating_mul, u32);
saturating_impl!(SaturatingMul, saturating_mul, u64);
saturating_impl!(SaturatingMul, saturating_mul, usize);
#[cfg(has_i128)]
saturating_impl!(SaturatingMul, saturating_mul, u128);

saturating_impl!(SaturatingMul, saturating_mul, i8);
saturating_impl!(SaturatingMul, saturating_mul, i16);
saturating_impl!(SaturatingMul, saturating_mul, i32);
saturating_impl!(SaturatingMul, saturating_mul, i64);
saturating_impl!(SaturatingMul, saturating_mul, isize);
#[cfg(has_i128)]
saturating_impl!(SaturatingMul, saturating_mul, i128);

// TODO: add SaturatingNeg for signed integer primitives once the saturating_neg() API is stable.

#[test]
fn test_saturating_traits() {
    fn saturating_add<T: SaturatingAdd>(a: T, b: T) -> T {
        a.saturating_add(&b)
    }
    fn saturating_sub<T: SaturatingSub>(a: T, b: T) -> T {
        a.saturating_sub(&b)
    }
    fn saturating_mul<T: SaturatingMul>(a: T, b: T) -> T {
        a.saturating_mul(&b)
    }
    assert_eq!(saturating_add(255, 1), 255u8);
    assert_eq!(saturating_add(127, 1), 127i8);
    assert_eq!(saturating_add(-128, -1), -128i8);
    assert_eq!(saturating_sub(0, 1), 0u8);
    assert_eq!(saturating_sub(-128, 1), -128i8);
    assert_eq!(saturating_sub(127, -1), 127i8);
    assert_eq!(saturating_mul(255, 2), 255u8);
    assert_eq!(saturating_mul(127, 2), 127i8);
    assert_eq!(saturating_mul(-128, 2), -128i8);
}
#[cfg(test)]
mod tests_rug_1719 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: isize = 9223372036854775807; // Sample data for isize, max value
        let mut p1: isize = 1; // Sample data for isize

        <isize as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1720 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: isize = 10;
        let mut p1: isize = 5;

        <isize as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1721 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = std::usize::MAX - 5;

        <usize as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1722 {
    use super::*;
    use crate::Saturating;
    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 3;

        <usize as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1723 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 125;
        let mut p1: i8 = 10;

        <i8 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1724 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 20;

        <i8 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1725 {
    use super::*;
    use crate::Saturating;
    
    #[test]
    fn test_rug() {
        let mut p0: u8 = 254;
        let mut p1: u8 = 3;

        <u8 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1726 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 3;

        <u8 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1727 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32760;
        let mut p1: i16 = 10;

        <i16 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1728 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 10;
        let mut p1: i16 = 5;

        <i16 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1729 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 65530;
        let mut p1: u16 = 10;

        let result = <u16 as Saturating>::saturating_add(p0, p1);
        assert_eq!(result, 65535); // Expected to saturate at the max value of u16
    }
}#[cfg(test)]
mod tests_rug_1730 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 10;
        let mut p1: u16 = 20;

        <u16 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1731 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2147483647; // Sample data for i32 max value
        let mut p1: i32 = 1;          // Sample data to cause saturation

        <i32 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1732 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 5;

        <i32 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1733 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // Sample data for u32, maximum value
        let mut p1: u32 = 1;          // Sample data for u32

        <u32 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1734 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 5;

        <u32 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1735 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 9223372036854775807; // Sample data for i64, maximum value
        let mut p1: i64 = 1;                   // Sample data for i64

        let result = <i64 as Saturating>::saturating_add(p0, p1);
        
        assert_eq!(result, 9223372036854775807); // Expected to saturate at max value
    }
}#[cfg(test)]
mod tests_rug_1736 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: i64 = 5;

        <i64 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1737 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u64 = 1; // Sample data for u64

        <u64 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1738 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 10;
        let mut p1: u64 = 5;

        <u64 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1739 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128
        let mut p1: i128 = 1; // Sample data for i128

        <i128 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1740 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 10;
        let mut p1: i128 = 5;

        <i128 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1741 {
    use super::*;
    use crate::ops::saturating::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615;
        let mut p1: u128 = 1;

        <u128 as Saturating>::saturating_add(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1742 {
    use super::*;
    use crate::Saturating;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 100;
        let mut p1: u128 = 50;

        <u128 as Saturating>::saturating_sub(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1743 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 250;
        let mut p1: u8 = 10;

        let result = <u8 as SaturatingAdd>::saturating_add(&p0, &p1);
        assert_eq!(result, 255);
    }
}#[cfg(test)]
mod tests_rug_1744 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 50000;
        let mut p1: u16 = 30000;

        let result = <u16 as SaturatingAdd>::saturating_add(&p0, &p1);
        assert_eq!(result, u16::MAX);
    }
}#[cfg(test)]
mod tests_rug_1745 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // Sample data for u32
        let mut p1: u32 = 1;          // Sample data for u32

        let result = <u32 as SaturatingAdd>::saturating_add(&p0, &p1);

        assert_eq!(result, 4294967295); // Expected result when adding 1 to u32::MAX
    }
}#[cfg(test)]
mod tests_rug_1746 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615;
        let mut p1: u64 = 1;

        let result = <u64 as SaturatingAdd>::saturating_add(&p0, &p1);

        assert_eq!(result, p0);
    }
}#[cfg(test)]
mod tests_rug_1747 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = std::usize::MAX;

        let result = <usize as SaturatingAdd>::saturating_add(&p0, &p1);
        
        assert_eq!(result, std::usize::MAX);
    }
}#[cfg(test)]
mod tests_rug_1748 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for max value of u128
        let mut p1: u128 = 1; // Sample data to cause saturation

        let result = <u128 as SaturatingAdd>::saturating_add(&p0, &p1);
        assert_eq!(result, p0); // Result should be the same as p0 due to saturation
    }
}#[cfg(test)]
mod tests_rug_1749 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 125;
        let mut p1: i8 = 10;

        let result = <i8 as SaturatingAdd>::saturating_add(&p0, &p1);
        assert_eq!(result, 127); // Expected result after saturating addition
    }
}#[cfg(test)]
mod tests_rug_1750 {
    use super::*;
    use crate::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32760;
        let mut p1: i16 = 10;

        let result = <i16 as SaturatingAdd>::saturating_add(&p0, &p1);
        assert_eq!(result, 32767); // Maximum value for i16
    }
}#[cfg(test)]
mod tests_rug_1751 {
    use super::*;
    use crate::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2147483647; // Sample data for the first argument
        let mut p1: i32 = 1;         // Sample data for the second argument

        let result = <i32 as SaturatingAdd>::saturating_add(&p0, &p1);
        assert_eq!(result, 2147483647); // Check that it saturates at the maximum value
    }
}#[cfg(test)]
mod tests_rug_1752 {
    use super::*;
    use crate::ops::saturating::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 9223372036854775807; // Sample data for i64
        let mut p1: i64 = 1;                  // Sample data for i64

        let result = <i64 as SaturatingAdd>::saturating_add(&p0, &p1);

        assert_eq!(result, 9223372036854775807); // Expected result after saturating addition
    }
}#[cfg(test)]
mod tests_rug_1753 {
    use super::*;
    use crate::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123;
        let mut p1: isize = std::isize::MAX;

        let result = <isize as SaturatingAdd>::saturating_add(&p0, &p1);
        
        assert_eq!(result, std::isize::MAX);
    }
}#[cfg(test)]
mod tests_rug_1754 {
    use super::*;
    use crate::SaturatingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128
        let mut p1: i128 = 1;                  // Sample data for i128

        let result = <i128 as SaturatingAdd>::saturating_add(&p0, &p1);

        assert_eq!(result, 9223372036854775807); // Check that it saturates
    }
}#[cfg(test)]
mod tests_rug_1755 {
    use super::*;
    use crate::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 10;
        let mut p1: u8 = 5;

        let result = <u8 as SaturatingSub>::saturating_sub(&p0, &p1);
        assert_eq!(result, 5);

        // Test saturating behavior
        let p2: u8 = 10;
        let p3: u8 = 15;
        let result_saturating = <u8 as SaturatingSub>::saturating_sub(&p2, &p3);
        assert_eq!(result_saturating, 0);
    }
}#[cfg(test)]
mod tests_rug_1756 {
    use super::*;
    use crate::ops::saturating::SaturatingSub;

    #[test]
    fn test_saturating_sub() {
        let mut p0: u16 = 10;
        let mut p1: u16 = 20;

        let result = <u16 as SaturatingSub>::saturating_sub(&p0, &p1);

        assert_eq!(result, 0);
    }
}#[cfg(test)]
mod tests_rug_1757 {
    use super::*;
    use crate::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 5;

        let result = <u32 as SaturatingSub>::saturating_sub(&p0, &p1);
        assert_eq!(result, 5);
    }
}#[cfg(test)]
mod tests_rug_1758 {
    use super::*;
    use crate::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 10;
        let mut p1: u64 = 5;

        let result = <u64 as SaturatingSub>::saturating_sub(&p0, &p1);
        assert_eq!(result, 5);
    }
}#[cfg(test)]
mod tests_rug_1759 {
    use super::*;
    use crate::ops::saturating::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 5;

        let result = <usize as SaturatingSub>::saturating_sub(&p0, &p1);
        assert_eq!(result, 5);

        // Test saturating behavior
        let p2: usize = 10;
        let p3: usize = 15;
        let result_saturated = <usize as SaturatingSub>::saturating_sub(&p2, &p3);
        assert_eq!(result_saturated, 0);
    }
}#[cfg(test)]
mod tests_rug_1760 {
    use super::*;
    use crate::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 100;
        let mut p1: u128 = 50;

        let result = <u128 as SaturatingSub>::saturating_sub(&p0, &p1);
        assert_eq!(result, 50);

        // Test saturating behavior
        let mut p2: u128 = 0;
        let mut p3: u128 = 1;

        let result_saturated = <u128 as SaturatingSub>::saturating_sub(&p2, &p3);
        assert_eq!(result_saturated, 0);
    }
}#[cfg(test)]
mod tests_rug_1761 {
    use super::*;
    use crate::ops::saturating::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 20;

        let result = <i8 as SaturatingSub>::saturating_sub(&p0, &p1);

        assert_eq!(result, i8::MIN); // Expected result when 10 - 20 saturates
    }
}#[cfg(test)]
mod tests_rug_1762 {
    use super::*;
    use crate::ops::saturating::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 5;
        let mut p1: i16 = 3;

        <i16 as SaturatingSub>::saturating_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1763 {
    use super::*;
    use crate::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 5;

        let result = <i32 as SaturatingSub>::saturating_sub(&p0, &p1);
        assert_eq!(result, 5);
    }
}#[cfg(test)]
mod tests_rug_1764 {
    use super::*;
    use crate::ops::saturating::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: i64 = 20;

        <i64 as SaturatingSub>::saturating_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1765 {
    use super::*;
    use crate::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: isize = 10;
        let mut p1: isize = 5;

        <isize as SaturatingSub>::saturating_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1766 {
    use super::*;
    use crate::ops::saturating::SaturatingSub;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 10;
        let mut p1: i128 = 5;

        <i128 as SaturatingSub>::saturating_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1767 {
    use super::*;
    use crate::ops::saturating::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 254;
        let mut p1: u8 = 2;

        <u8 as SaturatingMul>::saturating_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1768 {
    use super::*;
    use crate::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 32768;
        let mut p1: u16 = 2;

        <u16 as SaturatingMul>::saturating_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1769 {
    use super::*;
    use crate::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // u32::MAX
        let mut p1: u32 = 2;

        let result = <u32 as SaturatingMul>::saturating_mul(&p0, &p1);
        assert_eq!(result, 4294967295); // Expected to saturate at u32::MAX
    }
}#[cfg(test)]
mod tests_rug_1770 {
    use super::*;
    use crate::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18_446_744_073_709_551_615; // Sample data for u64 max value
        let mut p1: u64 = 2; // Sample data

        let result = <u64 as SaturatingMul>::saturating_mul(&p0, &p1);
        
        assert_eq!(result, 18_446_744_073_709_551_615); // Expected result due to saturation
    }
}#[cfg(test)]
mod tests_rug_1771 {
    use super::*;
    use crate::ops::saturating::SaturatingMul;

    #[test]
    fn test_saturating_mul() {
        let mut p0: usize = 10;
        let mut p1: usize = std::usize::MAX / 2 + 1;

        let result = <usize as SaturatingMul>::saturating_mul(&p0, &p1);
        
        assert_eq!(result, std::usize::MAX);
    }
}#[cfg(test)]
mod tests_rug_1772 {
    use super::*;
    use crate::ops::saturating::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128 (max value)
        let mut p1: u128 = 2; // Sample data for u128

        let result = <u128 as SaturatingMul>::saturating_mul(&p0, &p1);
        assert_eq!(result, 18446744073709551615); // Expected result due to saturation
    }
}#[cfg(test)]
mod tests_rug_1773 {
    use super::*;
    use crate::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 100;
        let mut p1: i8 = 2;

        p0.saturating_mul(p1);
    }
}#[cfg(test)]
mod tests_rug_1774 {
    use super::*;
    use crate::ops::saturating::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767;
        let mut p1: i16 = 2;

        let result = <i16 as SaturatingMul>::saturating_mul(&p0, &p1);
        assert_eq!(result, i16::MAX); // Expected to saturate at i16::MAX
    }
}#[cfg(test)]
mod tests_rug_1775 {
    use super::*;
    use crate::ops::saturating::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;
        let mut p1: i32 = 20;

        <i32 as SaturatingMul>::saturating_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1776 {
    use super::*;
    use crate::ops::saturating::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: i64 = 20;

        let result = <i64 as SaturatingMul>::saturating_mul(&p0, &p1);
        assert_eq!(result, 200);
    }
}#[cfg(test)]
mod tests_rug_1777 {
    use super::*;
    use crate::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: isize = 10;
        let mut p1: isize = 20;

        <isize as SaturatingMul>::saturating_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1778 {
    use super::*;
    use crate::SaturatingMul;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807;
        let mut p1: i128 = 2;

        let result = <i128 as SaturatingMul>::saturating_mul(&p0, &p1);
        assert_eq!(result, i128::MAX);
    }
}