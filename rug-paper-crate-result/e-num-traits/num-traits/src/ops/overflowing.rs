use core::ops::{Add, Mul, Sub};
#[cfg(has_i128)]
use core::{i128, u128};
use core::{i16, i32, i64, i8, isize};
use core::{u16, u32, u64, u8, usize};

macro_rules! overflowing_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &Self) -> (Self, bool) {
                <$t>::$method(*self, *v)
            }
        }
    };
}

/// Performs addition with a flag for overflow.
pub trait OverflowingAdd: Sized + Add<Self, Output = Self> {
    /// Returns a tuple of the sum along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_add(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingAdd, overflowing_add, u8);
overflowing_impl!(OverflowingAdd, overflowing_add, u16);
overflowing_impl!(OverflowingAdd, overflowing_add, u32);
overflowing_impl!(OverflowingAdd, overflowing_add, u64);
overflowing_impl!(OverflowingAdd, overflowing_add, usize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingAdd, overflowing_add, u128);

overflowing_impl!(OverflowingAdd, overflowing_add, i8);
overflowing_impl!(OverflowingAdd, overflowing_add, i16);
overflowing_impl!(OverflowingAdd, overflowing_add, i32);
overflowing_impl!(OverflowingAdd, overflowing_add, i64);
overflowing_impl!(OverflowingAdd, overflowing_add, isize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingAdd, overflowing_add, i128);

/// Performs substraction with a flag for overflow.
pub trait OverflowingSub: Sized + Sub<Self, Output = Self> {
    /// Returns a tuple of the difference along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_sub(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingSub, overflowing_sub, u8);
overflowing_impl!(OverflowingSub, overflowing_sub, u16);
overflowing_impl!(OverflowingSub, overflowing_sub, u32);
overflowing_impl!(OverflowingSub, overflowing_sub, u64);
overflowing_impl!(OverflowingSub, overflowing_sub, usize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingSub, overflowing_sub, u128);

overflowing_impl!(OverflowingSub, overflowing_sub, i8);
overflowing_impl!(OverflowingSub, overflowing_sub, i16);
overflowing_impl!(OverflowingSub, overflowing_sub, i32);
overflowing_impl!(OverflowingSub, overflowing_sub, i64);
overflowing_impl!(OverflowingSub, overflowing_sub, isize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingSub, overflowing_sub, i128);

/// Performs multiplication with a flag for overflow.
pub trait OverflowingMul: Sized + Mul<Self, Output = Self> {
    /// Returns a tuple of the product along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_mul(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingMul, overflowing_mul, u8);
overflowing_impl!(OverflowingMul, overflowing_mul, u16);
overflowing_impl!(OverflowingMul, overflowing_mul, u32);
overflowing_impl!(OverflowingMul, overflowing_mul, u64);
overflowing_impl!(OverflowingMul, overflowing_mul, usize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingMul, overflowing_mul, u128);

overflowing_impl!(OverflowingMul, overflowing_mul, i8);
overflowing_impl!(OverflowingMul, overflowing_mul, i16);
overflowing_impl!(OverflowingMul, overflowing_mul, i32);
overflowing_impl!(OverflowingMul, overflowing_mul, i64);
overflowing_impl!(OverflowingMul, overflowing_mul, isize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingMul, overflowing_mul, i128);

#[test]
fn test_overflowing_traits() {
    fn overflowing_add<T: OverflowingAdd>(a: T, b: T) -> (T, bool) {
        a.overflowing_add(&b)
    }
    fn overflowing_sub<T: OverflowingSub>(a: T, b: T) -> (T, bool) {
        a.overflowing_sub(&b)
    }
    fn overflowing_mul<T: OverflowingMul>(a: T, b: T) -> (T, bool) {
        a.overflowing_mul(&b)
    }
    assert_eq!(overflowing_add(5i16, 2), (7, false));
    assert_eq!(overflowing_add(i16::MAX, 1), (i16::MIN, true));
    assert_eq!(overflowing_sub(5i16, 2), (3, false));
    assert_eq!(overflowing_sub(i16::MIN, 1), (i16::MAX, true));
    assert_eq!(overflowing_mul(5i16, 2), (10, false));
    assert_eq!(overflowing_mul(1_000_000_000i32, 10), (1410065408, true));
}
#[cfg(test)]
mod tests_rug_1683 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 254;
        let mut p1: u8 = 3;

        <u8 as OverflowingAdd>::overflowing_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1684 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 65530;
        let mut p1: u16 = 10;

        let result = <u16 as OverflowingAdd>::overflowing_add(&p0, &p1);
        
        assert_eq!(result, (4, true));
    }
}#[cfg(test)]
mod tests_rug_1685 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // Sample data for u32, maximum value
        let mut p1: u32 = 1;           // Sample data for u32

        <u32 as OverflowingAdd>::overflowing_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1686 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18_446_744_073_709_551_615; // u64::MAX
        let mut p1: u64 = 1;

        let result = <u64 as OverflowingAdd>::overflowing_add(&p0, &p1);

        assert_eq!(result, (0, true));
    }
}#[cfg(test)]
mod tests_rug_1687 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: usize = 18446744073709551615; // Example large value for usize
        let mut p1: usize = 1; // Example small increment

        <usize as OverflowingAdd>::overflowing_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1688 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128
        let mut p1: u128 = 1;                    // Sample data for u128

        let (result, overflowed) = <u128 as OverflowingAdd>::overflowing_add(&p0, &p1);

        assert_eq!(result, 0);
        assert_eq!(overflowed, true);
    }
}#[cfg(test)]
mod tests_rug_1689 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;
        let mut p1: i8 = 1;

        let result = <i8 as OverflowingAdd>::overflowing_add(&p0, &p1);

        assert_eq!(result, (-128, true));
    }
}#[cfg(test)]
mod tests_rug_1690 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767;
        let mut p1: i16 = 1;

        let result = <i16 as OverflowingAdd>::overflowing_add(&p0, &p1);

        assert_eq!(result, (-32768, true));
    }
}#[cfg(test)]
mod tests_rug_1691 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2147483647; // Sample data for the first argument
        let mut p1: i32 = 1;         // Sample data for the second argument

        let (result, overflowed) = <i32 as OverflowingAdd>::overflowing_add(&p0, &p1);

        assert_eq!(result, -2147483648);
        assert_eq!(overflowed, true);
    }
}#[cfg(test)]
mod tests_rug_1692 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 9223372036854775807; // Sample data for the first argument
        let mut p1: i64 = 1;                   // Sample data for the second argument

        <i64 as OverflowingAdd>::overflowing_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1693 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: isize = 9223372036854775807; // Maximum value for isize on a 64-bit system
        let mut p1: isize = 1;

        <isize as OverflowingAdd>::overflowing_add(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1694 {
    use super::*;
    use crate::ops::overflowing::OverflowingAdd;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128
        let mut p1: i128 = 1;                   // Sample data for i128

        let result = <i128 as OverflowingAdd>::overflowing_add(&p0, &p1);
        assert_eq!(result, (9223372036854775808, true));
    }
}#[cfg(test)]
mod tests_rug_1695 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: u8 = 10;

        <u8 as OverflowingSub>::overflowing_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1696 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 10;
        let mut p1: u16 = 20;

        let result = <u16 as OverflowingSub>::overflowing_sub(&p0, &p1);
        assert_eq!(result, (65526, true)); // 10 - 20 overflows to 65536 - 10 = 65526
    }
}#[cfg(test)]
mod tests_rug_1697 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 10;
        let mut p1: u32 = 5;

        let result = <u32 as OverflowingSub>::overflowing_sub(&p0, &p1);

        assert_eq!(result, (5, false));
    }
}#[cfg(test)]
mod tests_rug_1698 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 10;
        let mut p1: u64 = 20;

        <u64 as OverflowingSub>::overflowing_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1699 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = 5;

        <usize as OverflowingSub>::overflowing_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1700 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128
        let mut p1: u128 = 1;                    // Sample data for u128

        let result = <u128 as OverflowingSub>::overflowing_sub(&p0, &p1);
        
        assert_eq!(result, (18446744073709551614, false));
    }
}#[cfg(test)]
mod tests_rug_1701 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 10;
        let mut p1: i8 = 20;

        <i8 as OverflowingSub>::overflowing_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1702 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767;
        let mut p1: i16 = -32768;

        let result = <i16 as OverflowingSub>::overflowing_sub(&p0, &p1);
        assert_eq!(result, (-1, true));
    }
}#[cfg(test)]
mod tests_rug_1703 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let p0: i32 = 10;
        let p1: i32 = 20;

        let result = <i32 as OverflowingSub>::overflowing_sub(&p0, &p1);

        // You can add assertions here if needed
        assert_eq!(result, (-10, false));
    }
}#[cfg(test)]
mod tests_rug_1704 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 10;
        let mut p1: i64 = 20;

        <i64 as OverflowingSub>::overflowing_sub(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1705 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: isize = 10;
        let mut p1: isize = 20;

        let result = <isize as OverflowingSub>::overflowing_sub(&p0, &p1);
        assert_eq!(result, (-10, true));
    }
}#[cfg(test)]
mod tests_rug_1706 {
    use super::*;
    use crate::ops::overflowing::OverflowingSub;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807;
        let mut p1: i128 = -9223372036854775808;

        let result = <i128 as OverflowingSub>::overflowing_sub(&p0, &p1);

        assert_eq!(result, (-1, true));
    }
}#[cfg(test)]
mod tests_rug_1707 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 254;
        let mut p1: u8 = 3;

        <u8 as OverflowingMul>::overflowing_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1708 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 32768;
        let mut p1: u16 = 2;

        let result = <u16 as OverflowingMul>::overflowing_mul(&p0, &p1);
        assert_eq!(result, (0, true));
    }
}#[cfg(test)]
mod tests_rug_1709 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // Sample data for u32, maximum value
        let mut p1: u32 = 2;         // Sample data for u32

        let (result, overflowed) = <u32 as OverflowingMul>::overflowing_mul(&p0, &p1);

        assert_eq!(result, 1);
        assert_eq!(overflowed, true);
    }
}#[cfg(test)]
mod tests_rug_1710 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u64 = 2; // Sample data for u64

        <u64 as OverflowingMul>::overflowing_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1711 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: usize = 10;
        let mut p1: usize = std::usize::MAX;

        <usize as OverflowingMul>::overflowing_mul(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_1712 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;
        let mut p1: u128 = 98765432109876543210987654321098765432;

        let result = <u128 as OverflowingMul>::overflowing_mul(&p0, &p1);
        assert_eq!(result, (p0.overflowing_mul(p1).0, p0.overflowing_mul(p1).1));
    }
}#[cfg(test)]
mod tests_rug_1713 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;
        let mut p1: i8 = 2;

        let (result, overflowed) = <i8 as OverflowingMul>::overflowing_mul(&p0, &p1);

        assert_eq!(result, -2);
        assert_eq!(overflowed, true);
    }
}#[cfg(test)]
mod tests_rug_1714 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767;
        let mut p1: i16 = 2;

        let (result, overflowed) = <i16 as OverflowingMul>::overflowing_mul(&p0, &p1);

        assert_eq!(result, -2);
        assert_eq!(overflowed, true);
    }
}#[cfg(test)]
mod tests_rug_1715 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 1_000_000;
        let mut p1: i32 = 10;

        let (result, overflowed) = <i32 as OverflowingMul>::overflowing_mul(&p0, &p1);

        assert_eq!(result, 10_000_000);
        assert_eq!(overflowed, false);
    }
}#[cfg(test)]
mod tests_rug_1716 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 9223372036854775807; // Max i64 value
        let mut p1: i64 = 2; // Multiplier that will cause overflow

        let (result, overflowed) = <i64 as OverflowingMul>::overflowing_mul(&p0, &p1);

        assert_eq!(result, -2);
        assert_eq!(overflowed, true);
    }
}#[cfg(test)]
mod tests_rug_1717 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789;
        let mut p1: isize = 987654321;

        let (result, overflowed) = <isize as OverflowingMul>::overflowing_mul(&p0, &p1);

        // Example assertions
        assert_eq!(result, -1152921504606846975);
        assert_eq!(overflowed, true);
    }
}#[cfg(test)]
mod tests_rug_1718 {
    use super::*;
    use crate::ops::overflowing::OverflowingMul;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807;
        let mut p1: i128 = 2;

        let result = <i128 as OverflowingMul>::overflowing_mul(&p0, &p1);
        assert_eq!(result, (-2, true));
    }
}