use core::ops::{BitAnd, BitOr, BitXor, Not, Shl, Shr};

use bounds::Bounded;
use ops::checked::*;
use ops::saturating::Saturating;
use {Num, NumCast};

/// Generic trait for primitive integers.
///
/// The `PrimInt` trait is an abstraction over the builtin primitive integer types (e.g., `u8`,
/// `u32`, `isize`, `i128`, ...). It inherits the basic numeric traits and extends them with
/// bitwise operators and non-wrapping arithmetic.
///
/// The trait explicitly inherits `Copy`, `Eq`, `Ord`, and `Sized`. The intention is that all
/// types implementing this trait behave like primitive types that are passed by value by default
/// and behave like builtin integers. Furthermore, the types are expected to expose the integer
/// value in binary representation and support bitwise operators. The standard bitwise operations
/// (e.g., bitwise-and, bitwise-or, right-shift, left-shift) are inherited and the trait extends
/// these with introspective queries (e.g., `PrimInt::count_ones()`, `PrimInt::leading_zeros()`),
/// bitwise combinators (e.g., `PrimInt::rotate_left()`), and endianness converters (e.g.,
/// `PrimInt::to_be()`).
///
/// All `PrimInt` types are expected to be fixed-width binary integers. The width can be queried
/// via `T::zero().count_zeros()`. The trait currently lacks a way to query the width at
/// compile-time.
///
/// While a default implementation for all builtin primitive integers is provided, the trait is in
/// no way restricted to these. Other integer types that fulfil the requirements are free to
/// implement the trait was well.
///
/// This trait and many of the method names originate in the unstable `core::num::Int` trait from
/// the rust standard library. The original trait was never stabilized and thus removed from the
/// standard library.
pub trait PrimInt:
    Sized
    + Copy
    + Num
    + NumCast
    + Bounded
    + PartialOrd
    + Ord
    + Eq
    + Not<Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitXor<Output = Self>
    + Shl<usize, Output = Self>
    + Shr<usize, Output = Self>
    + CheckedAdd<Output = Self>
    + CheckedSub<Output = Self>
    + CheckedMul<Output = Self>
    + CheckedDiv<Output = Self>
    + Saturating
{
    /// Returns the number of ones in the binary representation of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0b01001100u8;
    ///
    /// assert_eq!(n.count_ones(), 3);
    /// ```
    fn count_ones(self) -> u32;

    /// Returns the number of zeros in the binary representation of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0b01001100u8;
    ///
    /// assert_eq!(n.count_zeros(), 5);
    /// ```
    fn count_zeros(self) -> u32;

    /// Returns the number of leading ones in the binary representation
    /// of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0xF00Du16;
    ///
    /// assert_eq!(n.leading_ones(), 4);
    /// ```
    fn leading_ones(self) -> u32 {
        (!self).leading_zeros()
    }

    /// Returns the number of leading zeros in the binary representation
    /// of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0b0101000u16;
    ///
    /// assert_eq!(n.leading_zeros(), 10);
    /// ```
    fn leading_zeros(self) -> u32;

    /// Returns the number of trailing ones in the binary representation
    /// of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0xBEEFu16;
    ///
    /// assert_eq!(n.trailing_ones(), 4);
    /// ```
    fn trailing_ones(self) -> u32 {
        (!self).trailing_zeros()
    }

    /// Returns the number of trailing zeros in the binary representation
    /// of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0b0101000u16;
    ///
    /// assert_eq!(n.trailing_zeros(), 3);
    /// ```
    fn trailing_zeros(self) -> u32;

    /// Shifts the bits to the left by a specified amount, `n`, wrapping
    /// the truncated bits to the end of the resulting integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    /// let m = 0x3456789ABCDEF012u64;
    ///
    /// assert_eq!(n.rotate_left(12), m);
    /// ```
    fn rotate_left(self, n: u32) -> Self;

    /// Shifts the bits to the right by a specified amount, `n`, wrapping
    /// the truncated bits to the beginning of the resulting integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    /// let m = 0xDEF0123456789ABCu64;
    ///
    /// assert_eq!(n.rotate_right(12), m);
    /// ```
    fn rotate_right(self, n: u32) -> Self;

    /// Shifts the bits to the left by a specified amount, `n`, filling
    /// zeros in the least significant bits.
    ///
    /// This is bitwise equivalent to signed `Shl`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    /// let m = 0x3456789ABCDEF000u64;
    ///
    /// assert_eq!(n.signed_shl(12), m);
    /// ```
    fn signed_shl(self, n: u32) -> Self;

    /// Shifts the bits to the right by a specified amount, `n`, copying
    /// the "sign bit" in the most significant bits even for unsigned types.
    ///
    /// This is bitwise equivalent to signed `Shr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0xFEDCBA9876543210u64;
    /// let m = 0xFFFFEDCBA9876543u64;
    ///
    /// assert_eq!(n.signed_shr(12), m);
    /// ```
    fn signed_shr(self, n: u32) -> Self;

    /// Shifts the bits to the left by a specified amount, `n`, filling
    /// zeros in the least significant bits.
    ///
    /// This is bitwise equivalent to unsigned `Shl`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFi64;
    /// let m = 0x3456789ABCDEF000i64;
    ///
    /// assert_eq!(n.unsigned_shl(12), m);
    /// ```
    fn unsigned_shl(self, n: u32) -> Self;

    /// Shifts the bits to the right by a specified amount, `n`, filling
    /// zeros in the most significant bits.
    ///
    /// This is bitwise equivalent to unsigned `Shr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = -8i8; // 0b11111000
    /// let m = 62i8; // 0b00111110
    ///
    /// assert_eq!(n.unsigned_shr(2), m);
    /// ```
    fn unsigned_shr(self, n: u32) -> Self;

    /// Reverses the byte order of the integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    /// let m = 0xEFCDAB8967452301u64;
    ///
    /// assert_eq!(n.swap_bytes(), m);
    /// ```
    fn swap_bytes(self) -> Self;

    /// Reverses the order of bits in the integer.
    ///
    /// The least significant bit becomes the most significant bit, second least-significant bit
    /// becomes second most-significant bit, etc.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x12345678u32;
    /// let m = 0x1e6a2c48u32;
    ///
    /// assert_eq!(n.reverse_bits(), m);
    /// assert_eq!(0u32.reverse_bits(), 0);
    /// ```
    fn reverse_bits(self) -> Self {
        reverse_bits_fallback(self)
    }

    /// Convert an integer from big endian to the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    ///
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(u64::from_be(n), n)
    /// } else {
    ///     assert_eq!(u64::from_be(n), n.swap_bytes())
    /// }
    /// ```
    fn from_be(x: Self) -> Self;

    /// Convert an integer from little endian to the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    ///
    /// if cfg!(target_endian = "little") {
    ///     assert_eq!(u64::from_le(n), n)
    /// } else {
    ///     assert_eq!(u64::from_le(n), n.swap_bytes())
    /// }
    /// ```
    fn from_le(x: Self) -> Self;

    /// Convert `self` to big endian from the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    ///
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(n.to_be(), n)
    /// } else {
    ///     assert_eq!(n.to_be(), n.swap_bytes())
    /// }
    /// ```
    fn to_be(self) -> Self;

    /// Convert `self` to little endian from the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// let n = 0x0123456789ABCDEFu64;
    ///
    /// if cfg!(target_endian = "little") {
    ///     assert_eq!(n.to_le(), n)
    /// } else {
    ///     assert_eq!(n.to_le(), n.swap_bytes())
    /// }
    /// ```
    fn to_le(self) -> Self;

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::PrimInt;
    ///
    /// assert_eq!(2i32.pow(4), 16);
    /// ```
    fn pow(self, exp: u32) -> Self;
}

fn one_per_byte<P: PrimInt>() -> P {
    // i8, u8: return 0x01
    // i16, u16: return 0x0101 = (0x01 << 8) | 0x01
    // i32, u32: return 0x01010101 = (0x0101 << 16) | 0x0101
    // ...
    let mut ret = P::one();
    let mut shift = 8;
    let mut b = ret.count_zeros() >> 3;
    while b != 0 {
        ret = (ret << shift) | ret;
        shift <<= 1;
        b >>= 1;
    }
    ret
}

fn reverse_bits_fallback<P: PrimInt>(i: P) -> P {
    let rep_01: P = one_per_byte();
    let rep_03 = (rep_01 << 1) | rep_01;
    let rep_05 = (rep_01 << 2) | rep_01;
    let rep_0f = (rep_03 << 2) | rep_03;
    let rep_33 = (rep_03 << 4) | rep_03;
    let rep_55 = (rep_05 << 4) | rep_05;

    // code above only used to determine rep_0f, rep_33, rep_55;
    // optimizer should be able to do it in compile time
    let mut ret = i.swap_bytes();
    ret = ((ret & rep_0f) << 4) | ((ret >> 4) & rep_0f);
    ret = ((ret & rep_33) << 2) | ((ret >> 2) & rep_33);
    ret = ((ret & rep_55) << 1) | ((ret >> 1) & rep_55);
    ret
}

macro_rules! prim_int_impl {
    ($T:ty, $S:ty, $U:ty) => {
        impl PrimInt for $T {
            #[inline]
            fn count_ones(self) -> u32 {
                <$T>::count_ones(self)
            }

            #[inline]
            fn count_zeros(self) -> u32 {
                <$T>::count_zeros(self)
            }

            #[cfg(has_leading_trailing_ones)]
            #[inline]
            fn leading_ones(self) -> u32 {
                <$T>::leading_ones(self)
            }

            #[inline]
            fn leading_zeros(self) -> u32 {
                <$T>::leading_zeros(self)
            }

            #[cfg(has_leading_trailing_ones)]
            #[inline]
            fn trailing_ones(self) -> u32 {
                <$T>::trailing_ones(self)
            }

            #[inline]
            fn trailing_zeros(self) -> u32 {
                <$T>::trailing_zeros(self)
            }

            #[inline]
            fn rotate_left(self, n: u32) -> Self {
                <$T>::rotate_left(self, n)
            }

            #[inline]
            fn rotate_right(self, n: u32) -> Self {
                <$T>::rotate_right(self, n)
            }

            #[inline]
            fn signed_shl(self, n: u32) -> Self {
                ((self as $S) << n) as $T
            }

            #[inline]
            fn signed_shr(self, n: u32) -> Self {
                ((self as $S) >> n) as $T
            }

            #[inline]
            fn unsigned_shl(self, n: u32) -> Self {
                ((self as $U) << n) as $T
            }

            #[inline]
            fn unsigned_shr(self, n: u32) -> Self {
                ((self as $U) >> n) as $T
            }

            #[inline]
            fn swap_bytes(self) -> Self {
                <$T>::swap_bytes(self)
            }

            #[cfg(has_reverse_bits)]
            #[inline]
            fn reverse_bits(self) -> Self {
                <$T>::reverse_bits(self)
            }

            #[inline]
            fn from_be(x: Self) -> Self {
                <$T>::from_be(x)
            }

            #[inline]
            fn from_le(x: Self) -> Self {
                <$T>::from_le(x)
            }

            #[inline]
            fn to_be(self) -> Self {
                <$T>::to_be(self)
            }

            #[inline]
            fn to_le(self) -> Self {
                <$T>::to_le(self)
            }

            #[inline]
            fn pow(self, exp: u32) -> Self {
                <$T>::pow(self, exp)
            }
        }
    };
}

// prim_int_impl!(type, signed, unsigned);
prim_int_impl!(u8, i8, u8);
prim_int_impl!(u16, i16, u16);
prim_int_impl!(u32, i32, u32);
prim_int_impl!(u64, i64, u64);
#[cfg(has_i128)]
prim_int_impl!(u128, i128, u128);
prim_int_impl!(usize, isize, usize);
prim_int_impl!(i8, i8, u8);
prim_int_impl!(i16, i16, u16);
prim_int_impl!(i32, i32, u32);
prim_int_impl!(i64, i64, u64);
#[cfg(has_i128)]
prim_int_impl!(i128, i128, u128);
prim_int_impl!(isize, isize, usize);

#[cfg(test)]
mod tests {
    use int::PrimInt;

    #[test]
    pub fn reverse_bits() {
        use core::{i16, i32, i64, i8};

        assert_eq!(
            PrimInt::reverse_bits(0x0123_4567_89ab_cdefu64),
            0xf7b3_d591_e6a2_c480
        );

        assert_eq!(PrimInt::reverse_bits(0i8), 0);
        assert_eq!(PrimInt::reverse_bits(-1i8), -1);
        assert_eq!(PrimInt::reverse_bits(1i8), i8::MIN);
        assert_eq!(PrimInt::reverse_bits(i8::MIN), 1);
        assert_eq!(PrimInt::reverse_bits(-2i8), i8::MAX);
        assert_eq!(PrimInt::reverse_bits(i8::MAX), -2);

        assert_eq!(PrimInt::reverse_bits(0i16), 0);
        assert_eq!(PrimInt::reverse_bits(-1i16), -1);
        assert_eq!(PrimInt::reverse_bits(1i16), i16::MIN);
        assert_eq!(PrimInt::reverse_bits(i16::MIN), 1);
        assert_eq!(PrimInt::reverse_bits(-2i16), i16::MAX);
        assert_eq!(PrimInt::reverse_bits(i16::MAX), -2);

        assert_eq!(PrimInt::reverse_bits(0i32), 0);
        assert_eq!(PrimInt::reverse_bits(-1i32), -1);
        assert_eq!(PrimInt::reverse_bits(1i32), i32::MIN);
        assert_eq!(PrimInt::reverse_bits(i32::MIN), 1);
        assert_eq!(PrimInt::reverse_bits(-2i32), i32::MAX);
        assert_eq!(PrimInt::reverse_bits(i32::MAX), -2);

        assert_eq!(PrimInt::reverse_bits(0i64), 0);
        assert_eq!(PrimInt::reverse_bits(-1i64), -1);
        assert_eq!(PrimInt::reverse_bits(1i64), i64::MIN);
        assert_eq!(PrimInt::reverse_bits(i64::MIN), 1);
        assert_eq!(PrimInt::reverse_bits(-2i64), i64::MAX);
        assert_eq!(PrimInt::reverse_bits(i64::MAX), -2);
    }

    #[test]
    #[cfg(has_i128)]
    pub fn reverse_bits_i128() {
        use core::i128;

        assert_eq!(PrimInt::reverse_bits(0i128), 0);
        assert_eq!(PrimInt::reverse_bits(-1i128), -1);
        assert_eq!(PrimInt::reverse_bits(1i128), i128::MIN);
        assert_eq!(PrimInt::reverse_bits(i128::MIN), 1);
        assert_eq!(PrimInt::reverse_bits(-2i128), i128::MAX);
        assert_eq!(PrimInt::reverse_bits(i128::MAX), -2);
    }
}
#[cfg(test)]
mod tests_rug_783 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_one_per_byte_i8() {
        let result: i8 = crate::int::one_per_byte();
        assert_eq!(result, 0x01);
    }

    #[test]
    fn test_one_per_byte_u8() {
        let result: u8 = crate::int::one_per_byte();
        assert_eq!(result, 0x01);
    }

    #[test]
    fn test_one_per_byte_i16() {
        let result: i16 = crate::int::one_per_byte();
        assert_eq!(result, 0x0101);
    }

    #[test]
    fn test_one_per_byte_u16() {
        let result: u16 = crate::int::one_per_byte();
        assert_eq!(result, 0x0101);
    }

    #[test]
    fn test_one_per_byte_i32() {
        let result: i32 = crate::int::one_per_byte();
        assert_eq!(result, 0x01010101);
    }

    #[test]
    fn test_one_per_byte_u32() {
        let result: u32 = crate::int::one_per_byte();
        assert_eq!(result, 0x01010101);
    }
}#[cfg(test)]
mod tests_rug_784 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_reverse_bits_fallback() {
        let p0: u32 = 0x12345678;

        let result = crate::int::reverse_bits_fallback(p0);
        assert_eq!(result, 0x1e6a2c48);

        let p1: u64 = 0x0123456789ABCDEF;
        let result = crate::int::reverse_bits_fallback(p1);
        assert_eq!(result, 0xFEDCBA9876543210);

        let p2: u16 = 0xABCD;
        let result = crate::int::reverse_bits_fallback(p2);
        assert_eq!(result, 0xD5BA);

        let p3: u8 = 0b10101010;
        let result = crate::int::reverse_bits_fallback(p3);
        assert_eq!(result, 0b01010101);

        let p4: i32 = -1; // All bits set to 1
        let result = crate::int::reverse_bits_fallback(p4);
        assert_eq!(result, -1);

        let p5: i8 = 0;
        let result = crate::int::reverse_bits_fallback(p5);
        assert_eq!(result, 0);
    }
}#[cfg(test)]
mod tests_rug_788 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0b10101010;

        <u8 as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_789 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; // Sample data for u8

        <u8 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_790 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 255; // 255 in binary is 11111111, which has 8 leading ones

        <u8 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_791 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0b0011_1100; // Sample data for u8

        <u8 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_792 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0b00001111; // Example sample data for u8

        <u8 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_793 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0b0101_1000; // Sample data

        <u8 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_794 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0b1010_1010;
        let mut p1: u32 = 2;

        <u8 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_795 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;
        let mut p1: u32 = 5;

        <u8 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_796 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: u32 = 2;

        <u8 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_797 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 16;
        let mut p1: u32 = 2;

        <u8 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_798 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: u32 = 2;

        <u8 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_799 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 16;
        let mut p1: u32 = 2;

        <u8 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_800 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0x12;

        <u8>::swap_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_801 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0b1010_1010;

        <u8 as PrimInt>::reverse_bits(p0);
    }
}#[cfg(test)]
mod tests_rug_802 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0b1010_1010; // Sample data for u8

        <u8 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_803 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; 

        <u8 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_804 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u8 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_805 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u8 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_806 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 5;
        let mut p1: u32 = 3;

        <u8 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_807 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42; // Sample value for u16

        assert_eq!(<u16 as PrimInt>::count_ones(p0), p0.count_ones());
    }
}#[cfg(test)]
mod tests_rug_808 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 0b01010101; // Sample data to initialize the variable

        <u16 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_809 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u16 = 0b1111_0000; // Example sample data for u16 with leading ones

        <u16 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_810 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u16 = 0b0000_0000_1100_1100; // Sample data for u16

        <u16 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_811 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 0b0000_0111; // Sample data initializing p0

        <u16 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_812 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u16 = 0b0101_1000; // Sample data

        <u16 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_813 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 0b0001_1011;
        let mut p1: u32 = 2;

        <u16 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_814 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rotate_right() {
        let mut p0: u16 = 0b0000_1111_0000_1111;
        let mut p1: u32 = 4;

        <u16 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_815 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 5;
        let mut p1: u32 = 2;

        <u16 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_816 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 0b1010_1010_1010_1010;
        let mut p1: u32 = 4;

        <u16 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_817 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;
        let mut p1: u32 = 3;

        <u16 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_818 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;
        let mut p1: u32 = 3;

        <u16 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_819 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u16 = 0x1234;

        <u16 as PrimInt>::swap_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_820 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_reverse_bits() {
        let mut p0: u16 = 0b0000_1111_0000_1111;

        let result = <u16 as PrimInt>::reverse_bits(p0);

        // Example assertion, you can change it based on your needs
        assert_eq!(result, 0b1111_0000_1111_0000);
    }
}#[cfg(test)]
mod tests_rug_821 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u16 = 0x1234;

        <u16 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_822 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 0x1234;

        <u16 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_823 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 0xABCD;

        <u16 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_824 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 43690; // Sample data for u16

        <u16 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_825 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 4;
        let mut p1: u32 = 3;

        <u16 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_826 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; // Sample data for u32

        <u32 as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_827 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0b101010; // Sample data for initialization

        <u32 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_828 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0b11110000; // Sample data for u32

        <u32 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_829 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0b0010_1000_0000_0000_0000_0000_0000_0000;

        <u32 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_830 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0b0000_1111; // Sample data for u32 with trailing ones

        <u32 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_831 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; // Sample data for u32

        <u32 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_832 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0b0001_1010; // Sample data for a u32
        let mut p1: u32 = 3;            // Sample rotation amount

        <u32 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_833 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0b11110000;
        let mut p1: u32 = 4;

        <u32 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_834 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4; // Sample data for u32
        let mut p1: u32 = 2; // Sample data for u32

        <u32 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_835 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // Sample data for u32 (all bits set)
        let mut p1: u32 = 1;           // Sample data for u32

        <u32 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_836 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_unsigned_shl() {
        let mut p0: u32 = 42;
        let mut p1: u32 = 5;

        <u32 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_837 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;
        let mut p1: u32 = 3;

        <u32 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_838 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0x12345678u32;

        <u32 as PrimInt>::swap_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_839 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0b10101010101010101010101010101010; // Sample data

        let result = <u32 as PrimInt>::reverse_bits(p0);
        assert_eq!(result, 0b01010101010101010101010101010101); // Expected reversed bits
    }
}#[cfg(test)]
mod tests_rug_840 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0x1A2B3C4D;

        <u32 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_841 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u32 = 0x12345678;

        <u32 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_842 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 123456789;

        <u32 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_843 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 123456789;

        <u32 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_844 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 5;
        let mut p1: u32 = 3;

        <u32 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_845 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 29; // Example value for u64

        <u64 as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_846 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0b101010; // Sample data for a u64

        <u64 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_847 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0b1111_0000_1111_0000_1111_0000_1111_0000; // Sample data for u64

        <u64 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_848 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u64 = 0b1000_0000_0000_0000_0000_0000_0000_0000; // Example value

        assert_eq!(<u64 as PrimInt>::leading_zeros(p0), 31);
    }
}#[cfg(test)]
mod tests_rug_849 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_trailing_ones() {
        let mut p0: u64 = 0b110000; // Sample data for u64

        assert_eq!(<u64 as PrimInt>::trailing_ones(p0), 3);
    }
}#[cfg(test)]
mod tests_rug_850 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0b101000; // Sample data for u64

        <u64 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_851 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0b0001_1010_1100_1111_0000_1010_1010_1011;
        let mut p1: u32 = 5;

        <u64 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_852 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0b1111000011110000111100001111000011110000111100001111000011110000;
        let mut p1: u32 = 4;

        <u64 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_853 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u32 = 32; // Sample data for u32

        <u64 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_854 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0b1111_1111_1111_1111_1111_1111_1111_1111;
        let mut p1: u32 = 4;

        <u64 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_855 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 42;
        let mut p1: u32 = 5;

        <u64 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_856 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615; // Sample data for u64
        let mut p1: u32 = 32; // Sample data for u32

        <u64 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_857 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0x123456789ABCDEF0;

        <u64 as PrimInt>::swap_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_858 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0b1010_0000_1111_0000_0000_1111_0000_1010; // Sample data for a u64

        <u64 as PrimInt>::reverse_bits(p0);
    }
}#[cfg(test)]
mod tests_rug_859 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0x123456789abcdef0;

        <u64 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_860 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0x1234567890ABCDEFu64;

        <u64 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_861 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;

        <u64 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_862 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: u64 = 123456789;

        <u64 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_863 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_pow() {
        let mut p0: u64 = 2;
        let mut p1: u32 = 3;

        <u64 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_864 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0b1010101010101010101010101010101010101010101010101010101010101010;

        assert_eq!(<u128 as PrimInt>::count_ones(p0), 32);
    }
}#[cfg(test)]
mod tests_rug_865 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_0000;

        let result = <u128 as PrimInt>::count_zeros(p0);
        assert_eq!(result, 4);
    }
}#[cfg(test)]
mod tests_rug_866 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1110;

        let result = <u128 as PrimInt>::leading_ones(p0);

        assert_eq!(result, 127);
    }
}#[cfg(test)]
mod tests_rug_867 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1000;

        <u128 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_868 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_1111;

        let result = <u128 as PrimInt>::trailing_ones(p0);
        assert_eq!(result, 4);
    }
}#[cfg(test)]
mod tests_rug_869 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0b1010_0000u128; // Sample data with trailing zeros

        assert_eq!(<u128 as PrimInt>::trailing_zeros(p0), 3);
    }
}#[cfg(test)]
mod tests_rug_870 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0b1100110011001100110011001100110011001100110011001100110011001100;
        let mut p1: u32 = 4;

        let result = <u128 as PrimInt>::rotate_left(p0, p1);
        
        // You can add assertions here to verify the result if needed
    }
}#[cfg(test)]
mod tests_rug_871 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rotate_right() {
        let mut p0: u128 = 0x1234567890abcdef1234567890abcdef;
        let mut p1: u32 = 8;

        <u128 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_872 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_signed_shl() {
        let mut p0: u128 = 42;
        let mut p1: u32 = 5;

        <u128 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_873 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Example max value for u128
        let mut p1: u32 = 3; // Example shift amount

        <u128 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_874 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42;
        let mut p1: u32 = 5;

        <u128 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_875 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615u128; // Sample data for u128
        let mut p1: u32 = 32u32; // Sample data for u32

        <u128 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_876 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0x1234567890ABCDEF1234567890ABCDEF;

        let swapped = <u128 as PrimInt>::swap_bytes(p0);
        assert_eq!(swapped, 0xEFCDAB9078563412EFCDAB9078563412);
    }
}#[cfg(test)]
mod tests_rug_877 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_reverse_bits() {
        let mut p0: u128 = 0x1234_5678_9ABC_DEF0_ABCD_EF09_8765_4321;

        let result = <u128 as PrimInt>::reverse_bits(p0);

        // Optionally, you can add an assertion to check the result
        assert_eq!(result, 0x2143_6587_A9CF_EFDB_0FED_CBA9_8765_4321);
    }
}#[cfg(test)]
mod tests_rug_878 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0x1234567890ABCDEF1234567890ABCDEFu128;

        <u128 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_879 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0x1234567890abcdef1234567890abcdef;

        <u128 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_880 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0x112233445566778899AABBCCDDEEFF00;

        <u128 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_881 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0x123456789ABCDEF0u128;

        <u128 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_882 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 5;
        let mut p1: u32 = 3;

        <u128 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_883 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42; // Sample data for usize

        <usize as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_884 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0b101010; // Sample data for usize

        <usize as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_885 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0b11110000_11110000_11110000_11110000; // Sample data for demonstration

        <usize as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_886 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0b0001_0000_0000_0000_0000_0000_0000_0000; // Example sample data for usize

        <usize>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_887 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0b111_1000; // Sample data with trailing ones

        <usize as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_888 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_trailing_zeros() {
        let p0: usize = 18; // Sample data for usize

        assert_eq!(<usize as PrimInt>::trailing_zeros(p0), 1);
    }
}#[cfg(test)]
mod tests_rug_889 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0b0101_1010;
        let mut p1: u32 = 2;

        <usize>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_890 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0b1110_0000;
        let mut p1: u32 = 2;

        <usize as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_891 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;
        let mut p1: u32 = 3;

        <usize as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_892 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42; // Sample data for usize
        let mut p1: u32 = 2;   // Sample data for u32

        <usize as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_893 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;
        let mut p1: u32 = 5;

        <usize as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_894 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 16;
        let mut p1: u32 = 2;

        <usize as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_895 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0x12345678_9ABCDEF0;

        <usize>::swap_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_896 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0b1100101; // Sample data to initialize a usize variable

        <usize as PrimInt>::reverse_bits(p0);
    }
}#[cfg(test)]
mod tests_rug_897 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 123456789;

        <usize>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_898 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <usize>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_899 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <usize as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_900 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: usize = 1234567890;

        <usize as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_901 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_pow() {
        let mut p0: usize = 5;
        let mut p1: u32 = 3;

        <usize as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_902 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Example initialization

        <i8 as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_903 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -1; // Example initialization

        <i8 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_904 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -1; // Sample data for i8 with all bits set to 1

        <i8 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_905 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -128; // Sample data for i8

        <i8 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_906 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 0b0111; // Sample data for i8

        <i8 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_907 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -128; // Example initialization

        <i8 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_908 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;
        let mut p1: u32 = 5;

        <i8 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_909 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 16;   // Example value for i8
        let mut p1: u32 = 3;  // Example value for u32

        <i8 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_910 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 4;
        let mut p1: u32 = 2;

        <i8 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_911 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -16;
        let mut p1: u32 = 2;

        <i8 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_912 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 5;
        let mut p1: u32 = 2;

        <i8 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_913 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 16;
        let mut p1: u32 = 2;

        <i8 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_914 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 123; // Sample data for i8

        <i8 as PrimInt>::swap_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_915 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_reverse_bits() {
        let mut p0: i8 = 42; // Sample data for i8

        assert_eq!(p0.reverse_bits(), 0x51); // The expected result of reversing bits in 42
    }
}#[cfg(test)]
mod tests_rug_916 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 123_i8;

        <i8 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_917 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i8 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_918 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i8 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_919 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i8 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_920 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_pow() {
        let mut p0: i8 = 2;
        let mut p1: u32 = 3;

        <i8 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_921 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 29; // Example value for i16

        <i16 as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_922 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 0b0101_1010; // Sample data for initialization

        <i16 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_923 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = -1; // Example value for testing leading_ones

        <i16 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_924 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: i16 = 0b0000_0000_1111_1111; // Sample data

        <i16 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_925 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 0b0000_0000_0000_1111; // Sample data for i16

        <i16 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_926 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: i16 = 0b0100_0000; // Sample data for i16

        <i16 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_927 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;
        let mut p1: u32 = 5;

        <i16 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_928 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rotate_right() {
        let mut p0: i16 = 42;
        let mut p1: u32 = 5;

        <i16 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_929 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 4;
        let mut p1: u32 = 2;

        <i16 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_930 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = -8;
        let mut p1: u32 = 2;

        <i16 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_931 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;
        let mut p1: u32 = 5;

        <i16 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_932 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;
        let mut p1: u32 = 3;

        <i16 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_933 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 0x1234;

        let result = <i16 as PrimInt>::swap_bytes(p0);
        assert_eq!(result, 0x3412);
    }
}#[cfg(test)]
mod tests_rug_934 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 0b0000_0000_0000_1111; // Example sample data

        <i16 as PrimInt>::reverse_bits(p0);
    }
}#[cfg(test)]
mod tests_rug_935 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 0x1234;

        <i16 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_936 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: i16 = 0x1234;

        <i16 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_937 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        <i16 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_938 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        <i16 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_939 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 2;
        let mut p1: u32 = 3;

        <i16 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_940 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42; // Sample data for i32

        <i32 as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_941 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 0b101010; // Sample data for i32

        <i32 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_942 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = -1; // All bits set to 1, which is a common sample for testing leading ones

        <i32 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_943 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42; // Sample initialization

        <i32 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_944 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 0b0011_1100; // Sample data to initialize p0

        <i32 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_945 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 16; // Example value for i32

        assert_eq!(<i32 as PrimInt>::trailing_zeros(p0), 4);
    }
}#[cfg(test)]
mod tests_rug_946 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 0x12345678;
        let mut p1: u32 = 4;

        <i32 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_947 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 16;
        let mut p1: u32 = 2;

        <i32 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_948 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = -5;
        let mut p1: u32 = 3;

        <i32 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_949 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;
        let mut p1: u32 = 3;

        <i32 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_950 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 16;
        let mut p1: u32 = 2;

        <i32 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_951 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = -16;  // Sample data for i32
        let mut p1: u32 = 2;   // Sample data for u32

        <i32 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_952 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 0x12345678;

        let result = <i32 as PrimInt>::swap_bytes(p0);
        assert_eq!(result, 0x78563412);
    }
}#[cfg(test)]
mod tests_rug_953 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 0b00000000_00000001_00000000_00000010; // Sample data for i32

        <i32 as PrimInt>::reverse_bits(p0);
    }
}#[cfg(test)]
mod tests_rug_954 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 0x12345678;

        <i32 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_955 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 0x12345678;

        <i32 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_956 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        <i32 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_957 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        <i32 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_958 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 2;
        let mut p1: u32 = 3;

        <i32 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_959 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 29; // Example value for i64

        <i64 as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_960 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 0b101010; // Sample binary data for i64

        <i64 as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_961 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = -1; // Sample data for i64 that has all bits set to 1

        <i64 as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_962 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: i64 = 0b0110_0000_0000_0000_0000_0000_0000_0000;

        <i64 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_963 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_trailing_ones() {
        let mut p0: i64 = 0b11110000; // Sample data to initialize p0

        <i64 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_964 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = -128; // Sample data

        <i64 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_965 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 0x123456789abcdef0;
        let mut p1: u32 = 8;

        <i64 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_966 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 0x1234567890ABCDEF;
        let mut p1: u32 = 8;

        <i64 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_967 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 15;
        let mut p1: u32 = 2;

        <i64 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_968 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1024;
        let mut p1: u32 = 3;

        <i64 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_969 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 15;
        let mut p1: u32 = 2;

        <i64 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_970 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456;
        let mut p1: u32 = 8;

        <i64 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_971 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1234567890123456789;

        let result = <i64 as PrimInt>::swap_bytes(p0);

        // You can add assertions here to verify the result
        assert_eq!(result, 7890123456789012345); // This is just a placeholder assertion
    }
}#[cfg(test)]
mod tests_rug_972 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_reverse_bits() {
        let mut p0: i64 = 0b1101_1010_1011_0000_0001_0010_0010_0000;

        let result = <i64 as PrimInt>::reverse_bits(p0);
        assert_eq!(result, 0b0000_0010_0010_0010_0001_0000_1011_0110);
    }
}#[cfg(test)]
mod tests_rug_973 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 0x123456789ABCDEF0;

        <i64 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_974 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        <i64 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_975 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        <i64 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_976 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        <i64 as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_977 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_pow() {
        let mut p0: i64 = 2;
        let mut p1: u32 = 3;

        <i64 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_978 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42; // Sample data for i128

        let result = <i128 as PrimInt>::count_ones(p0);
        assert_eq!(result, 3); // The binary representation of 42 is 101010, which has three 1s.
    }
}#[cfg(test)]
mod tests_rug_979 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0b1010101010101010101010101010101010101010101010101010101010101010;

        let result = <i128 as PrimInt>::count_zeros(p0);
        
        assert_eq!(result, 64); // Example assertion, adjust based on expected result
    }
}#[cfg(test)]
mod tests_rug_980 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0b1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1110;

        let result = <i128 as PrimInt>::leading_ones(p0);
        assert_eq!(result, 127);
    }
}#[cfg(test)]
mod tests_rug_981 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: i128 = -1;

        <i128 as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_982 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0b00001111; // Sample data for testing trailing_ones

        <i128 as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_983 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0b101000;

        <i128 as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_984 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: u32 = 5;

        <i128 as PrimInt>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_985 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0x1234567890ABCDEF1234567890ABCDEF;
        let mut p1: u32 = 42;

        <i128 as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_986 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: u32 = 5;

        <i128 as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_987 {
    use super::*;
    use crate::int::PrimInt;

    #[test]
    fn test_signed_shr() {
        let mut p0: i128 = -42;
        let mut p1: u32 = 3;

        <i128 as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_988 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;
        let mut p1: u32 = 5;

        <i128 as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_989 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 456;
        let mut p1: u32 = 3;

        <i128 as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_990 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0x123456789ABCDEF0123456789ABCDEF0i128;

        <i128 as PrimInt>::swap_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_991 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_reverse_bits() {
        let mut p0: i128 = 0x123456789ABCDEF0;

        let reversed = <i128 as PrimInt>::reverse_bits(p0);
        assert_eq!(reversed, 0xF0DEBC9A78563412);
    }
}#[cfg(test)]
mod tests_rug_992 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0x1234567890ABCDEF1234567890ABCDEF;

        <i128 as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_993 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789;

        <i128 as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_994 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789;

        <i128 as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_995 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789;

        p0.to_le();
    }
}#[cfg(test)]
mod tests_rug_996 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 2;
        let mut p1: u32 = 3;

        <i128 as PrimInt>::pow(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_997 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42; // Sample data for isize

        <isize as PrimInt>::count_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_998 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: isize = 42; // Sample data

        <isize as PrimInt>::count_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_999 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: isize = -1; // Example value for isize with all bits set to 1

        <isize as PrimInt>::leading_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_1000 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let p0: isize = -1; // Example initialization of isize

        <isize as PrimInt>::leading_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_1001 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = -1; // Sample data for isize, all bits set to 1

        <isize as PrimInt>::trailing_ones(p0);
    }
}#[cfg(test)]
mod tests_rug_1002 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 16; // Example sample data for isize

        <isize as PrimInt>::trailing_zeros(p0);
    }
}#[cfg(test)]
mod tests_rug_1003 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: u32 = 5;

        <isize>::rotate_left(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1004 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: u32 = 5;

        <isize as PrimInt>::rotate_right(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1005 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: u32 = 3;

        <isize as PrimInt>::signed_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1006 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = -42;
        let mut p1: u32 = 3;

        <isize as PrimInt>::signed_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1007 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: u32 = 3;

        <isize as PrimInt>::unsigned_shl(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1008 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;
        let mut p1: u32 = 3;

        <isize as PrimInt>::unsigned_shr(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_1009 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 1234567890;

        let result = <isize>::swap_bytes(p0);

        // Optionally, you can add an assertion to check the result
        // For example, if running on a little-endian system:
        // assert_eq!(result, 0x1e240bed);
    }
}#[cfg(test)]
mod tests_rug_1010 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_reverse_bits() {
        let p0: isize = 0b1010_1010_1010_1010_1010_1010_1010_1010; // Sample data

        <isize as PrimInt>::reverse_bits(p0);
    }
}#[cfg(test)]
mod tests_rug_1011 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789;

        <isize as PrimInt>::from_be(p0);
    }
}#[cfg(test)]
mod tests_rug_1012 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42; // Sample data initialization

        <isize as PrimInt>::from_le(p0);
    }
}#[cfg(test)]
mod tests_rug_1013 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        <isize as PrimInt>::to_be(p0);
    }
}#[cfg(test)]
mod tests_rug_1014 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789;

        <isize as PrimInt>::to_le(p0);
    }
}#[cfg(test)]
mod tests_rug_1015 {
    use super::*;
    use crate::PrimInt;

    #[test]
    fn test_rug() {
        let mut p0: isize = 4;
        let mut p1: u32 = 2;

        <isize>::pow(p0, p1);
    }
}