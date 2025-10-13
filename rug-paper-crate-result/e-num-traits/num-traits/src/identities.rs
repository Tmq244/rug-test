use core::num::Wrapping;
use core::ops::{Add, Mul};

/// Defines an additive identity element for `Self`.
///
/// # Laws
///
/// ```{.text}
/// a + 0 = a       ∀ a ∈ Self
/// 0 + a = a       ∀ a ∈ Self
/// ```
pub trait Zero: Sized + Add<Self, Output = Self> {
    /// Returns the additive identity element of `Self`, `0`.
    /// # Purity
    ///
    /// This function should return the same result at all times regardless of
    /// external mutable state, for example values stored in TLS or in
    /// `static mut`s.
    // This cannot be an associated constant, because of bignums.
    fn zero() -> Self;

    /// Sets `self` to the additive identity element of `Self`, `0`.
    fn set_zero(&mut self) {
        *self = Zero::zero();
    }

    /// Returns `true` if `self` is equal to the additive identity.
    fn is_zero(&self) -> bool;
}

macro_rules! zero_impl {
    ($t:ty, $v:expr) => {
        impl Zero for $t {
            #[inline]
            fn zero() -> $t {
                $v
            }
            #[inline]
            fn is_zero(&self) -> bool {
                *self == $v
            }
        }
    };
}

zero_impl!(usize, 0);
zero_impl!(u8, 0);
zero_impl!(u16, 0);
zero_impl!(u32, 0);
zero_impl!(u64, 0);
#[cfg(has_i128)]
zero_impl!(u128, 0);

zero_impl!(isize, 0);
zero_impl!(i8, 0);
zero_impl!(i16, 0);
zero_impl!(i32, 0);
zero_impl!(i64, 0);
#[cfg(has_i128)]
zero_impl!(i128, 0);

zero_impl!(f32, 0.0);
zero_impl!(f64, 0.0);

impl<T: Zero> Zero for Wrapping<T>
where
    Wrapping<T>: Add<Output = Wrapping<T>>,
{
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    fn set_zero(&mut self) {
        self.0.set_zero();
    }

    fn zero() -> Self {
        Wrapping(T::zero())
    }
}

/// Defines a multiplicative identity element for `Self`.
///
/// # Laws
///
/// ```{.text}
/// a * 1 = a       ∀ a ∈ Self
/// 1 * a = a       ∀ a ∈ Self
/// ```
pub trait One: Sized + Mul<Self, Output = Self> {
    /// Returns the multiplicative identity element of `Self`, `1`.
    ///
    /// # Purity
    ///
    /// This function should return the same result at all times regardless of
    /// external mutable state, for example values stored in TLS or in
    /// `static mut`s.
    // This cannot be an associated constant, because of bignums.
    fn one() -> Self;

    /// Sets `self` to the multiplicative identity element of `Self`, `1`.
    fn set_one(&mut self) {
        *self = One::one();
    }

    /// Returns `true` if `self` is equal to the multiplicative identity.
    ///
    /// For performance reasons, it's best to implement this manually.
    /// After a semver bump, this method will be required, and the
    /// `where Self: PartialEq` bound will be removed.
    #[inline]
    fn is_one(&self) -> bool
    where
        Self: PartialEq,
    {
        *self == Self::one()
    }
}

macro_rules! one_impl {
    ($t:ty, $v:expr) => {
        impl One for $t {
            #[inline]
            fn one() -> $t {
                $v
            }
            #[inline]
            fn is_one(&self) -> bool {
                *self == $v
            }
        }
    };
}

one_impl!(usize, 1);
one_impl!(u8, 1);
one_impl!(u16, 1);
one_impl!(u32, 1);
one_impl!(u64, 1);
#[cfg(has_i128)]
one_impl!(u128, 1);

one_impl!(isize, 1);
one_impl!(i8, 1);
one_impl!(i16, 1);
one_impl!(i32, 1);
one_impl!(i64, 1);
#[cfg(has_i128)]
one_impl!(i128, 1);

one_impl!(f32, 1.0);
one_impl!(f64, 1.0);

impl<T: One> One for Wrapping<T>
where
    Wrapping<T>: Mul<Output = Wrapping<T>>,
{
    fn set_one(&mut self) {
        self.0.set_one();
    }

    fn one() -> Self {
        Wrapping(T::one())
    }
}

// Some helper functions provided for backwards compatibility.

/// Returns the additive identity, `0`.
#[inline(always)]
pub fn zero<T: Zero>() -> T {
    Zero::zero()
}

/// Returns the multiplicative identity, `1`.
#[inline(always)]
pub fn one<T: One>() -> T {
    One::one()
}

#[test]
fn wrapping_identities() {
    macro_rules! test_wrapping_identities {
        ($($t:ty)+) => {
            $(
                assert_eq!(zero::<$t>(), zero::<Wrapping<$t>>().0);
                assert_eq!(one::<$t>(), one::<Wrapping<$t>>().0);
                assert_eq!((0 as $t).is_zero(), Wrapping(0 as $t).is_zero());
                assert_eq!((1 as $t).is_zero(), Wrapping(1 as $t).is_zero());
            )+
        };
    }

    test_wrapping_identities!(isize i8 i16 i32 i64 usize u8 u16 u32 u64);
}

#[test]
fn wrapping_is_zero() {
    fn require_zero<T: Zero>(_: &T) {}
    require_zero(&Wrapping(42));
}
#[test]
fn wrapping_is_one() {
    fn require_one<T: One>(_: &T) {}
    require_one(&Wrapping(42));
}
#[cfg(test)]
mod tests_rug_717 {
    use super::*;
    use crate::{Zero, identities};

    #[test]
    fn test_rug() {
        let int_value: i32 = 0;
        let float_value: f64 = 0.0;
        let unsigned_value: u32 = 0;

        assert_eq!(identities::zero::<i32>(), int_value);
        assert_eq!(identities::zero::<f64>(), float_value);
        assert_eq!(identities::zero::<u32>(), unsigned_value);
    }
}#[cfg(test)]
mod tests_rug_718 {
    use super::*;
    use crate::One;
    
    #[test]
    fn test_rug() {
        let x: i32 = 0; // Sample variable of type i32, can be any integer type that implements One
        let y: f64 = 0.0; // Sample variable of type f64, can be any floating point type that implements One

        let one_i32: i32 = crate::identities::one();
        let one_f64: f64 = crate::identities::one();

        assert_eq!(one_i32, 1);
        assert_eq!(one_f64, 1.0);
    }
}#[cfg(test)]
mod tests_rug_719 {
    use super::*;
    use crate::{Zero, Add};
    use core::marker::Sized;

    #[test]
    fn test_set_zero() {
        let mut p0: i32 = 42; // Concrete implementation that satisfies the bounds

        crate::identities::Zero::set_zero(&mut p0);

        assert_eq!(p0, 0);
    }
}#[cfg(test)]
mod tests_rug_720 {
    use super::*;
    use crate::identities::One;
    use std::ops::Mul;

    // A simple concrete implementation of the One trait for testing purposes
    #[derive(Debug, PartialEq)]
    struct TestNumber(u32);

    impl One for TestNumber {
        fn one() -> Self {
            TestNumber(1)
        }
    }

    impl Mul<Self> for TestNumber {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            TestNumber(self.0 * rhs.0)
        }
    }

    #[test]
    fn test_set_one() {
        let mut p0: TestNumber = TestNumber(42);

        crate::identities::One::set_one(&mut p0);

        assert_eq!(p0, TestNumber(1));
    }
}#[cfg(test)]
mod tests_rug_721 {
    use super::*;
    use crate::identities::One;
    use core::ops::Mul;
    use core::cmp::PartialEq;

    #[derive(Debug, Clone, Copy, PartialEq)]
    struct MyNumber(i32);

    impl Mul for MyNumber {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self {
            MyNumber(self.0 * rhs.0)
        }
    }

    impl One for MyNumber {
        fn one() -> Self {
            MyNumber(1)
        }
    }

    #[test]
    fn test_rug() {
        let mut p0: MyNumber = MyNumber(1);

        assert!(One::is_one(&p0));

        p0 = MyNumber(2);
        assert!(!One::is_one(&p0));
    }
}#[cfg(test)]
mod tests_rug_722 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let zero_value: usize = <usize as Zero>::zero();
        
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_723 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: usize = 0;

        assert_eq!(<usize as Zero>::is_zero(&p0), true);

        p0 = 1;
        assert_eq!(<usize as Zero>::is_zero(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_724 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero_u8() {
        let zero_value: u8 = <u8 as Zero>::zero();
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_725 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0;

        assert_eq!(<u8 as Zero>::is_zero(&p0), true);

        p0 = 1;
        assert_eq!(<u8 as Zero>::is_zero(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_726 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let zero_value: u16 = <u16 as Zero>::zero();
        
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_727 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 0;

        assert!((<u16 as Zero>::is_zero(&p0)));

        p0 = 5;
        assert!(!(<u16 as Zero>::is_zero(&p0)));
    }
}#[cfg(test)]
mod tests_rug_728 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero_u32() {
        let result: u32 = <u32 as Zero>::zero();
        assert_eq!(result, 0);
    }
}#[cfg(test)]
mod tests_rug_729 {
    use super::*;
    use crate::Zero;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 0; // Sample data to initialize p0

        assert_eq!(<u32 as Zero>::is_zero(&p0), true);

        p0 = 42;
        assert_eq!(<u32 as Zero>::is_zero(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_730 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let zero_value: u64 = <u64 as Zero>::zero();
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_731 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 0;

        assert!((<u64 as Zero>::is_zero(&p0)));

        p0 = 1;
        assert!(!(<u64 as Zero>::is_zero(&p0)));
    }
}#[cfg(test)]
mod tests_rug_732 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let zero_value: u128 = <u128 as Zero>::zero();
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_733 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 0;

        assert!(<u128 as Zero>::is_zero(&p0));

        p0 = 42;
        assert!(!<u128 as Zero>::is_zero(&p0));
    }
}#[cfg(test)]
mod tests_rug_734 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero_isize() {
        let zero_value: isize = <isize as Zero>::zero();
        
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_735 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let p0: isize = 0;

        assert!((<isize as Zero>::is_zero(&p0)));
        
        let p1: isize = 42;
        
        assert!(!(<isize as Zero>::is_zero(&p1)));
    }
}#[cfg(test)]
mod tests_rug_736 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero_for_i8() {
        let zero_value: i8 = <i8 as Zero>::zero();
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_737 {
    use super::*;
    use crate::Zero;

    #[test]
    fn test_rug() {
        let p0: i8 = 0;

        assert!(<i8 as Zero>::is_zero(&p0));

        let p1: i8 = 5;
        
        assert!(!<i8 as Zero>::is_zero(&p1));
    }
}#[cfg(test)]
mod tests_rug_738 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let zero_value: i16 = <i16 as Zero>::zero();

        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_739 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let p0: i16 = 0;

        assert_eq!(<i16 as Zero>::is_zero(&p0), true);

        let p1: i16 = 42;
        assert_eq!(<i16 as Zero>::is_zero(&p1), false);
    }
}#[cfg(test)]
mod tests_rug_740 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let result: i32 = <i32 as Zero>::zero();
        assert_eq!(result, 0);
    }
}#[cfg(test)]
mod tests_rug_741 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let p0: i32 = 0;

        assert_eq!(<i32 as Zero>::is_zero(&p0), true);

        let p1: i32 = 42;

        assert_eq!(<i32 as Zero>::is_zero(&p1), false);
    }
}#[cfg(test)]
mod tests_rug_742 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let result: i64 = <i64 as Zero>::zero();
        assert_eq!(result, 0);
    }
}#[cfg(test)]
mod tests_rug_743 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 0;

        assert!((<i64 as Zero>::is_zero)(&p0));

        p0 = 1;
        assert!(!(<i64 as Zero>::is_zero)(&p0));
    }
}#[cfg(test)]
mod tests_rug_744 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let zero_value: i128 = <i128 as Zero>::zero();
        assert_eq!(zero_value, 0);
    }
}#[cfg(test)]
mod tests_rug_745 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 0;

        assert_eq!(<i128 as Zero>::is_zero(&p0), true);
        
        p0 = 123;
        assert_eq!(<i128 as Zero>::is_zero(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_746 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero() {
        let zero_value: f32 = <f32 as Zero>::zero();
        
        assert_eq!(zero_value, 0.0);
    }
}#[cfg(test)]
mod tests_rug_747 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 0.0;

        assert!(<f32 as Zero>::is_zero(&p0));

        p0 = 1.0;
        assert!(!<f32 as Zero>::is_zero(&p0));
    }
}#[cfg(test)]
mod tests_rug_748 {
    use super::*;
    use crate::identities::Zero;

    #[test]
    fn test_zero_f64() {
        let zero_value: f64 = <f64 as Zero>::zero();
        assert_eq!(zero_value, 0.0);
    }
}#[cfg(test)]
mod tests_rug_749 {
    use super::*;
    use crate::Zero;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 0.0;

        assert!((<f64 as Zero>::is_zero(&p0)));
        
        p0 = 1.0;
        assert!(!(<f64 as Zero>::is_zero(&p0)));

        p0 = -0.0;
        assert!((<f64 as Zero>::is_zero(&p0)));

        p0 = f64::NAN;
        assert!(!(<f64 as Zero>::is_zero(&p0)));

        p0 = f64::INFINITY;
        assert!(!(<f64 as Zero>::is_zero(&p0)));

        p0 = f64::NEG_INFINITY;
        assert!(!(<f64 as Zero>::is_zero(&p0)));
    }
}#[cfg(test)]
mod tests_rug_752 {
    use super::*;
    use crate::identities::Zero;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let wrapping_zero_u8: Wrapping<u8> = <Wrapping<u8>>::zero();
        let wrapping_zero_i32: Wrapping<i32> = <Wrapping<i32>>::zero();

        assert_eq!(wrapping_zero_u8.0, 0u8);
        assert_eq!(wrapping_zero_i32.0, 0i32);
    }
}#[cfg(test)]
mod tests_rug_753 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_one() {
        let result: usize = <usize as One>::one();
        assert_eq!(result, 1);
    }
}#[cfg(test)]
mod tests_rug_754 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let mut p0: usize = 1;

        assert_eq!(<usize as One>::is_one(&p0), true);

        p0 = 2;
        assert_eq!(<usize as One>::is_one(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_755 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let result: u8 = <u8 as One>::one();
        assert_eq!(result, 1);
    }
}#[cfg(test)]
mod tests_rug_756 {
    use super::*;
    use crate::One;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 1;

        assert!(<u8 as One>::is_one(&p0));

        let p1: u8 = 0;
        assert!(!<u8 as One>::is_one(&p1));
    }
}#[cfg(test)]
mod tests_rug_757 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let one_u16: u16 = <u16 as One>::one();

        assert_eq!(one_u16, 1);
    }
}#[cfg(test)]
mod tests_rug_758 {
    use super::*;
    use crate::One;

    #[test]
    fn test_rug() {
        let p0: u16 = 1;

        assert!((<u16 as One>::is_one)(&p0));
    }
}#[cfg(test)]
mod tests_rug_759 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let one_u32: u32 = <u32 as One>::one();

        assert_eq!(one_u32, 1);
    }
}#[cfg(test)]
mod tests_rug_760 {
    use super::*;
    use crate::One;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 1;

        assert!((<u32 as One>::is_one(&p0)));
        
        p0 = 0;
        assert!(!(<u32 as One>::is_one(&p0)));
    }
}#[cfg(test)]
mod tests_rug_761 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let one_value: u64 = <u64 as One>::one();

        assert_eq!(one_value, 1);
    }
}#[cfg(test)]
mod tests_rug_762 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1;

        assert_eq!(<u64 as One>::is_one(&p0), true);

        p0 = 2;
        assert_eq!(<u64 as One>::is_one(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_763 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let one_u128: u128 = <u128 as One>::one();

        assert_eq!(one_u128, 1);
    }
}#[cfg(test)]
mod tests_rug_764 {
    use super::*;
    use crate::One;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 1u128;

        assert_eq!(<u128 as One>::is_one(&p0), true);
        
        p0 = 0u128;
        assert_eq!(<u128 as One>::is_one(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_765 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let one_value: isize = <isize as One>::one();
        
        assert_eq!(one_value, 1);
    }
}#[cfg(test)]
mod tests_rug_766 {
    use super::*;
    use crate::One;

    #[test]
    fn test_rug() {
        let mut p0: isize = 1;

        assert_eq!(<isize as One>::is_one(&p0), true);

        p0 = 0;
        assert_eq!(<isize as One>::is_one(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_767 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_one() {
        let result: i8 = <i8 as One>::one();
        assert_eq!(result, 1);
    }
}#[cfg(test)]
mod tests_rug_768 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let p0: i8 = 1;

        assert!(<i8 as One>::is_one(&p0));
        
        let p1: i8 = 0;
        assert!(!<i8 as One>::is_one(&p1));
    }
}#[cfg(test)]
mod tests_rug_769 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_one() {
        let result: i16 = <i16 as One>::one();
        assert_eq!(result, 1);
    }
}#[cfg(test)]
mod tests_rug_770 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 1;

        assert!(<i16 as One>::is_one(&p0));
        
        p0 = 2;
        assert!(!<i16 as One>::is_one(&p0));
    }
}#[cfg(test)]
mod tests_rug_771 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let one_value: i32 = <i32 as One>::one();

        assert_eq!(one_value, 1);
    }
}#[cfg(test)]
mod tests_rug_772 {
    use super::*;
    use crate::One;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 1;

        assert_eq!((<i32 as One>::is_one)(&p0), true);

        p0 = 0;
        assert_eq!((<i32 as One>::is_one)(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_773 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let value: i64 = <i64 as One>::one();

        assert_eq!(value, 1);
    }
}#[cfg(test)]
mod tests_rug_774 {
    use super::*;
    use crate::One;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1;

        assert_eq!(<i64 as One>::is_one(&p0), true);
        
        p0 = 0;
        assert_eq!(<i64 as One>::is_one(&p0), false);

        p0 = -1;
        assert_eq!(<i64 as One>::is_one(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_775 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let one_value: i128 = <i128 as One>::one();
        
        assert_eq!(one_value, 1);
    }
}#[cfg(test)]
mod tests_rug_776 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let p0: i128 = 1;

        assert_eq!(<i128 as One>::is_one(&p0), true);

        let p1: i128 = 0;
        assert_eq!(<i128 as One>::is_one(&p1), false);
    }
}#[cfg(test)]
mod tests_rug_777 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_one() {
        let one_value: f32 = <f32 as One>::one();
        
        assert_eq!(one_value, 1.0);
    }
}#[cfg(test)]
mod tests_rug_778 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 1.0;

        assert!(<f32 as One>::is_one(&p0));
    }
}#[cfg(test)]
mod tests_rug_779 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_one_f64() {
        let one_value: f64 = <f64 as One>::one();
        
        assert_eq!(one_value, 1.0);
    }
}#[cfg(test)]
mod tests_rug_780 {
    use super::*;
    use crate::identities::One;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 1.0;

        assert!((<f64 as One>::is_one(&p0)));
        
        p0 = 2.0;
        assert!(!(<f64 as One>::is_one(&p0)));
    }
}#[cfg(test)]
mod tests_rug_782 {
    use super::*;
    use crate::identities::One; // Corrected the path to identities::One
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let wrapping_u32: Wrapping<u32> = <Wrapping<u32>>::one();
        let wrapping_i32: Wrapping<i32> = <Wrapping<i32>>::one();

        assert_eq!(wrapping_u32, Wrapping(1u32));
        assert_eq!(wrapping_i32, Wrapping(1i32));
    }
}