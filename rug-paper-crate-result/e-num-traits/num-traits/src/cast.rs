use core::mem::size_of;
use core::num::Wrapping;
use core::{f32, f64};
#[cfg(has_i128)]
use core::{i128, u128};
use core::{i16, i32, i64, i8, isize};
use core::{u16, u32, u64, u8, usize};

/// A generic trait for converting a value to a number.
///
/// A value can be represented by the target type when it lies within
/// the range of scalars supported by the target type.
/// For example, a negative integer cannot be represented by an unsigned
/// integer type, and an `i64` with a very high magnitude might not be
/// convertible to an `i32`.
/// On the other hand, conversions with possible precision loss or truncation
/// are admitted, like an `f32` with a decimal part to an integer type, or
/// even a large `f64` saturating to `f32` infinity.
pub trait ToPrimitive {
    /// Converts the value of `self` to an `isize`. If the value cannot be
    /// represented by an `isize`, then `None` is returned.
    #[inline]
    fn to_isize(&self) -> Option<isize> {
        self.to_i64().as_ref().and_then(ToPrimitive::to_isize)
    }

    /// Converts the value of `self` to an `i8`. If the value cannot be
    /// represented by an `i8`, then `None` is returned.
    #[inline]
    fn to_i8(&self) -> Option<i8> {
        self.to_i64().as_ref().and_then(ToPrimitive::to_i8)
    }

    /// Converts the value of `self` to an `i16`. If the value cannot be
    /// represented by an `i16`, then `None` is returned.
    #[inline]
    fn to_i16(&self) -> Option<i16> {
        self.to_i64().as_ref().and_then(ToPrimitive::to_i16)
    }

    /// Converts the value of `self` to an `i32`. If the value cannot be
    /// represented by an `i32`, then `None` is returned.
    #[inline]
    fn to_i32(&self) -> Option<i32> {
        self.to_i64().as_ref().and_then(ToPrimitive::to_i32)
    }

    /// Converts the value of `self` to an `i64`. If the value cannot be
    /// represented by an `i64`, then `None` is returned.
    fn to_i64(&self) -> Option<i64>;

    /// Converts the value of `self` to an `i128`. If the value cannot be
    /// represented by an `i128` (`i64` under the default implementation), then
    /// `None` is returned.
    ///
    /// This method is only available with feature `i128` enabled on Rust >= 1.26.
    ///
    /// The default implementation converts through `to_i64()`. Types implementing
    /// this trait should override this method if they can represent a greater range.
    #[inline]
    #[cfg(has_i128)]
    fn to_i128(&self) -> Option<i128> {
        self.to_i64().map(From::from)
    }

    /// Converts the value of `self` to a `usize`. If the value cannot be
    /// represented by a `usize`, then `None` is returned.
    #[inline]
    fn to_usize(&self) -> Option<usize> {
        self.to_u64().as_ref().and_then(ToPrimitive::to_usize)
    }

    /// Converts the value of `self` to a `u8`. If the value cannot be
    /// represented by a `u8`, then `None` is returned.
    #[inline]
    fn to_u8(&self) -> Option<u8> {
        self.to_u64().as_ref().and_then(ToPrimitive::to_u8)
    }

    /// Converts the value of `self` to a `u16`. If the value cannot be
    /// represented by a `u16`, then `None` is returned.
    #[inline]
    fn to_u16(&self) -> Option<u16> {
        self.to_u64().as_ref().and_then(ToPrimitive::to_u16)
    }

    /// Converts the value of `self` to a `u32`. If the value cannot be
    /// represented by a `u32`, then `None` is returned.
    #[inline]
    fn to_u32(&self) -> Option<u32> {
        self.to_u64().as_ref().and_then(ToPrimitive::to_u32)
    }

    /// Converts the value of `self` to a `u64`. If the value cannot be
    /// represented by a `u64`, then `None` is returned.
    fn to_u64(&self) -> Option<u64>;

    /// Converts the value of `self` to a `u128`. If the value cannot be
    /// represented by a `u128` (`u64` under the default implementation), then
    /// `None` is returned.
    ///
    /// This method is only available with feature `i128` enabled on Rust >= 1.26.
    ///
    /// The default implementation converts through `to_u64()`. Types implementing
    /// this trait should override this method if they can represent a greater range.
    #[inline]
    #[cfg(has_i128)]
    fn to_u128(&self) -> Option<u128> {
        self.to_u64().map(From::from)
    }

    /// Converts the value of `self` to an `f32`. Overflows may map to positive
    /// or negative inifinity, otherwise `None` is returned if the value cannot
    /// be represented by an `f32`.
    #[inline]
    fn to_f32(&self) -> Option<f32> {
        self.to_f64().as_ref().and_then(ToPrimitive::to_f32)
    }

    /// Converts the value of `self` to an `f64`. Overflows may map to positive
    /// or negative inifinity, otherwise `None` is returned if the value cannot
    /// be represented by an `f64`.
    ///
    /// The default implementation tries to convert through `to_i64()`, and
    /// failing that through `to_u64()`. Types implementing this trait should
    /// override this method if they can represent a greater range.
    #[inline]
    fn to_f64(&self) -> Option<f64> {
        match self.to_i64() {
            Some(i) => i.to_f64(),
            None => self.to_u64().as_ref().and_then(ToPrimitive::to_f64),
        }
    }
}

macro_rules! impl_to_primitive_int_to_int {
    ($SrcT:ident : $( $(#[$cfg:meta])* fn $method:ident -> $DstT:ident ; )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(&self) -> Option<$DstT> {
            let min = $DstT::MIN as $SrcT;
            let max = $DstT::MAX as $SrcT;
            if size_of::<$SrcT>() <= size_of::<$DstT>() || (min <= *self && *self <= max) {
                Some(*self as $DstT)
            } else {
                None
            }
        }
    )*}
}

macro_rules! impl_to_primitive_int_to_uint {
    ($SrcT:ident : $( $(#[$cfg:meta])* fn $method:ident -> $DstT:ident ; )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(&self) -> Option<$DstT> {
            let max = $DstT::MAX as $SrcT;
            if 0 <= *self && (size_of::<$SrcT>() <= size_of::<$DstT>() || *self <= max) {
                Some(*self as $DstT)
            } else {
                None
            }
        }
    )*}
}

macro_rules! impl_to_primitive_int {
    ($T:ident) => {
        impl ToPrimitive for $T {
            impl_to_primitive_int_to_int! { $T:
                fn to_isize -> isize;
                fn to_i8 -> i8;
                fn to_i16 -> i16;
                fn to_i32 -> i32;
                fn to_i64 -> i64;
                #[cfg(has_i128)]
                fn to_i128 -> i128;
            }

            impl_to_primitive_int_to_uint! { $T:
                fn to_usize -> usize;
                fn to_u8 -> u8;
                fn to_u16 -> u16;
                fn to_u32 -> u32;
                fn to_u64 -> u64;
                #[cfg(has_i128)]
                fn to_u128 -> u128;
            }

            #[inline]
            fn to_f32(&self) -> Option<f32> {
                Some(*self as f32)
            }
            #[inline]
            fn to_f64(&self) -> Option<f64> {
                Some(*self as f64)
            }
        }
    };
}

impl_to_primitive_int!(isize);
impl_to_primitive_int!(i8);
impl_to_primitive_int!(i16);
impl_to_primitive_int!(i32);
impl_to_primitive_int!(i64);
#[cfg(has_i128)]
impl_to_primitive_int!(i128);

macro_rules! impl_to_primitive_uint_to_int {
    ($SrcT:ident : $( $(#[$cfg:meta])* fn $method:ident -> $DstT:ident ; )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(&self) -> Option<$DstT> {
            let max = $DstT::MAX as $SrcT;
            if size_of::<$SrcT>() < size_of::<$DstT>() || *self <= max {
                Some(*self as $DstT)
            } else {
                None
            }
        }
    )*}
}

macro_rules! impl_to_primitive_uint_to_uint {
    ($SrcT:ident : $( $(#[$cfg:meta])* fn $method:ident -> $DstT:ident ; )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(&self) -> Option<$DstT> {
            let max = $DstT::MAX as $SrcT;
            if size_of::<$SrcT>() <= size_of::<$DstT>() || *self <= max {
                Some(*self as $DstT)
            } else {
                None
            }
        }
    )*}
}

macro_rules! impl_to_primitive_uint {
    ($T:ident) => {
        impl ToPrimitive for $T {
            impl_to_primitive_uint_to_int! { $T:
                fn to_isize -> isize;
                fn to_i8 -> i8;
                fn to_i16 -> i16;
                fn to_i32 -> i32;
                fn to_i64 -> i64;
                #[cfg(has_i128)]
                fn to_i128 -> i128;
            }

            impl_to_primitive_uint_to_uint! { $T:
                fn to_usize -> usize;
                fn to_u8 -> u8;
                fn to_u16 -> u16;
                fn to_u32 -> u32;
                fn to_u64 -> u64;
                #[cfg(has_i128)]
                fn to_u128 -> u128;
            }

            #[inline]
            fn to_f32(&self) -> Option<f32> {
                Some(*self as f32)
            }
            #[inline]
            fn to_f64(&self) -> Option<f64> {
                Some(*self as f64)
            }
        }
    };
}

impl_to_primitive_uint!(usize);
impl_to_primitive_uint!(u8);
impl_to_primitive_uint!(u16);
impl_to_primitive_uint!(u32);
impl_to_primitive_uint!(u64);
#[cfg(has_i128)]
impl_to_primitive_uint!(u128);

macro_rules! impl_to_primitive_float_to_float {
    ($SrcT:ident : $( fn $method:ident -> $DstT:ident ; )*) => {$(
        #[inline]
        fn $method(&self) -> Option<$DstT> {
            // We can safely cast all values, whether NaN, +-inf, or finite.
            // Finite values that are reducing size may saturate to +-inf.
            Some(*self as $DstT)
        }
    )*}
}

#[cfg(has_to_int_unchecked)]
macro_rules! float_to_int_unchecked {
    // SAFETY: Must not be NaN or infinite; must be representable as the integer after truncating.
    // We already checked that the float is in the exclusive range `(MIN-1, MAX+1)`.
    ($float:expr => $int:ty) => {
        unsafe { $float.to_int_unchecked::<$int>() }
    };
}

#[cfg(not(has_to_int_unchecked))]
macro_rules! float_to_int_unchecked {
    ($float:expr => $int:ty) => {
        $float as $int
    };
}

macro_rules! impl_to_primitive_float_to_signed_int {
    ($f:ident : $( $(#[$cfg:meta])* fn $method:ident -> $i:ident ; )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(&self) -> Option<$i> {
            // Float as int truncates toward zero, so we want to allow values
            // in the exclusive range `(MIN-1, MAX+1)`.
            if size_of::<$f>() > size_of::<$i>() {
                // With a larger size, we can represent the range exactly.
                const MIN_M1: $f = $i::MIN as $f - 1.0;
                const MAX_P1: $f = $i::MAX as $f + 1.0;
                if *self > MIN_M1 && *self < MAX_P1 {
                    return Some(float_to_int_unchecked!(*self => $i));
                }
            } else {
                // We can't represent `MIN-1` exactly, but there's no fractional part
                // at this magnitude, so we can just use a `MIN` inclusive boundary.
                const MIN: $f = $i::MIN as $f;
                // We can't represent `MAX` exactly, but it will round up to exactly
                // `MAX+1` (a power of two) when we cast it.
                const MAX_P1: $f = $i::MAX as $f;
                if *self >= MIN && *self < MAX_P1 {
                    return Some(float_to_int_unchecked!(*self => $i));
                }
            }
            None
        }
    )*}
}

macro_rules! impl_to_primitive_float_to_unsigned_int {
    ($f:ident : $( $(#[$cfg:meta])* fn $method:ident -> $u:ident ; )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(&self) -> Option<$u> {
            // Float as int truncates toward zero, so we want to allow values
            // in the exclusive range `(-1, MAX+1)`.
            if size_of::<$f>() > size_of::<$u>() {
                // With a larger size, we can represent the range exactly.
                const MAX_P1: $f = $u::MAX as $f + 1.0;
                if *self > -1.0 && *self < MAX_P1 {
                    return Some(float_to_int_unchecked!(*self => $u));
                }
            } else {
                // We can't represent `MAX` exactly, but it will round up to exactly
                // `MAX+1` (a power of two) when we cast it.
                // (`u128::MAX as f32` is infinity, but this is still ok.)
                const MAX_P1: $f = $u::MAX as $f;
                if *self > -1.0 && *self < MAX_P1 {
                    return Some(float_to_int_unchecked!(*self => $u));
                }
            }
            None
        }
    )*}
}

macro_rules! impl_to_primitive_float {
    ($T:ident) => {
        impl ToPrimitive for $T {
            impl_to_primitive_float_to_signed_int! { $T:
                fn to_isize -> isize;
                fn to_i8 -> i8;
                fn to_i16 -> i16;
                fn to_i32 -> i32;
                fn to_i64 -> i64;
                #[cfg(has_i128)]
                fn to_i128 -> i128;
            }

            impl_to_primitive_float_to_unsigned_int! { $T:
                fn to_usize -> usize;
                fn to_u8 -> u8;
                fn to_u16 -> u16;
                fn to_u32 -> u32;
                fn to_u64 -> u64;
                #[cfg(has_i128)]
                fn to_u128 -> u128;
            }

            impl_to_primitive_float_to_float! { $T:
                fn to_f32 -> f32;
                fn to_f64 -> f64;
            }
        }
    };
}

impl_to_primitive_float!(f32);
impl_to_primitive_float!(f64);

/// A generic trait for converting a number to a value.
///
/// A value can be represented by the target type when it lies within
/// the range of scalars supported by the target type.
/// For example, a negative integer cannot be represented by an unsigned
/// integer type, and an `i64` with a very high magnitude might not be
/// convertible to an `i32`.
/// On the other hand, conversions with possible precision loss or truncation
/// are admitted, like an `f32` with a decimal part to an integer type, or
/// even a large `f64` saturating to `f32` infinity.
pub trait FromPrimitive: Sized {
    /// Converts an `isize` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_isize(n: isize) -> Option<Self> {
        n.to_i64().and_then(FromPrimitive::from_i64)
    }

    /// Converts an `i8` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_i8(n: i8) -> Option<Self> {
        FromPrimitive::from_i64(From::from(n))
    }

    /// Converts an `i16` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_i16(n: i16) -> Option<Self> {
        FromPrimitive::from_i64(From::from(n))
    }

    /// Converts an `i32` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_i32(n: i32) -> Option<Self> {
        FromPrimitive::from_i64(From::from(n))
    }

    /// Converts an `i64` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    fn from_i64(n: i64) -> Option<Self>;

    /// Converts an `i128` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    ///
    /// This method is only available with feature `i128` enabled on Rust >= 1.26.
    ///
    /// The default implementation converts through `from_i64()`. Types implementing
    /// this trait should override this method if they can represent a greater range.
    #[inline]
    #[cfg(has_i128)]
    fn from_i128(n: i128) -> Option<Self> {
        n.to_i64().and_then(FromPrimitive::from_i64)
    }

    /// Converts a `usize` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_usize(n: usize) -> Option<Self> {
        n.to_u64().and_then(FromPrimitive::from_u64)
    }

    /// Converts an `u8` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_u8(n: u8) -> Option<Self> {
        FromPrimitive::from_u64(From::from(n))
    }

    /// Converts an `u16` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_u16(n: u16) -> Option<Self> {
        FromPrimitive::from_u64(From::from(n))
    }

    /// Converts an `u32` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_u32(n: u32) -> Option<Self> {
        FromPrimitive::from_u64(From::from(n))
    }

    /// Converts an `u64` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    fn from_u64(n: u64) -> Option<Self>;

    /// Converts an `u128` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    ///
    /// This method is only available with feature `i128` enabled on Rust >= 1.26.
    ///
    /// The default implementation converts through `from_u64()`. Types implementing
    /// this trait should override this method if they can represent a greater range.
    #[inline]
    #[cfg(has_i128)]
    fn from_u128(n: u128) -> Option<Self> {
        n.to_u64().and_then(FromPrimitive::from_u64)
    }

    /// Converts a `f32` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    #[inline]
    fn from_f32(n: f32) -> Option<Self> {
        FromPrimitive::from_f64(From::from(n))
    }

    /// Converts a `f64` to return an optional value of this type. If the
    /// value cannot be represented by this type, then `None` is returned.
    ///
    /// The default implementation tries to convert through `from_i64()`, and
    /// failing that through `from_u64()`. Types implementing this trait should
    /// override this method if they can represent a greater range.
    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        match n.to_i64() {
            Some(i) => FromPrimitive::from_i64(i),
            None => n.to_u64().and_then(FromPrimitive::from_u64),
        }
    }
}

macro_rules! impl_from_primitive {
    ($T:ty, $to_ty:ident) => {
        #[allow(deprecated)]
        impl FromPrimitive for $T {
            #[inline]
            fn from_isize(n: isize) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_i8(n: i8) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_i16(n: i16) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_i32(n: i32) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_i64(n: i64) -> Option<$T> {
                n.$to_ty()
            }
            #[cfg(has_i128)]
            #[inline]
            fn from_i128(n: i128) -> Option<$T> {
                n.$to_ty()
            }

            #[inline]
            fn from_usize(n: usize) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_u8(n: u8) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_u16(n: u16) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_u32(n: u32) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_u64(n: u64) -> Option<$T> {
                n.$to_ty()
            }
            #[cfg(has_i128)]
            #[inline]
            fn from_u128(n: u128) -> Option<$T> {
                n.$to_ty()
            }

            #[inline]
            fn from_f32(n: f32) -> Option<$T> {
                n.$to_ty()
            }
            #[inline]
            fn from_f64(n: f64) -> Option<$T> {
                n.$to_ty()
            }
        }
    };
}

impl_from_primitive!(isize, to_isize);
impl_from_primitive!(i8, to_i8);
impl_from_primitive!(i16, to_i16);
impl_from_primitive!(i32, to_i32);
impl_from_primitive!(i64, to_i64);
#[cfg(has_i128)]
impl_from_primitive!(i128, to_i128);
impl_from_primitive!(usize, to_usize);
impl_from_primitive!(u8, to_u8);
impl_from_primitive!(u16, to_u16);
impl_from_primitive!(u32, to_u32);
impl_from_primitive!(u64, to_u64);
#[cfg(has_i128)]
impl_from_primitive!(u128, to_u128);
impl_from_primitive!(f32, to_f32);
impl_from_primitive!(f64, to_f64);

macro_rules! impl_to_primitive_wrapping {
    ($( $(#[$cfg:meta])* fn $method:ident -> $i:ident ; )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(&self) -> Option<$i> {
            (self.0).$method()
        }
    )*}
}

impl<T: ToPrimitive> ToPrimitive for Wrapping<T> {
    impl_to_primitive_wrapping! {
        fn to_isize -> isize;
        fn to_i8 -> i8;
        fn to_i16 -> i16;
        fn to_i32 -> i32;
        fn to_i64 -> i64;
        #[cfg(has_i128)]
        fn to_i128 -> i128;

        fn to_usize -> usize;
        fn to_u8 -> u8;
        fn to_u16 -> u16;
        fn to_u32 -> u32;
        fn to_u64 -> u64;
        #[cfg(has_i128)]
        fn to_u128 -> u128;

        fn to_f32 -> f32;
        fn to_f64 -> f64;
    }
}

macro_rules! impl_from_primitive_wrapping {
    ($( $(#[$cfg:meta])* fn $method:ident ( $i:ident ); )*) => {$(
        #[inline]
        $(#[$cfg])*
        fn $method(n: $i) -> Option<Self> {
            T::$method(n).map(Wrapping)
        }
    )*}
}

impl<T: FromPrimitive> FromPrimitive for Wrapping<T> {
    impl_from_primitive_wrapping! {
        fn from_isize(isize);
        fn from_i8(i8);
        fn from_i16(i16);
        fn from_i32(i32);
        fn from_i64(i64);
        #[cfg(has_i128)]
        fn from_i128(i128);

        fn from_usize(usize);
        fn from_u8(u8);
        fn from_u16(u16);
        fn from_u32(u32);
        fn from_u64(u64);
        #[cfg(has_i128)]
        fn from_u128(u128);

        fn from_f32(f32);
        fn from_f64(f64);
    }
}

/// Cast from one machine scalar to another.
///
/// # Examples
///
/// ```
/// # use num_traits as num;
/// let twenty: f32 = num::cast(0x14).unwrap();
/// assert_eq!(twenty, 20f32);
/// ```
///
#[inline]
pub fn cast<T: NumCast, U: NumCast>(n: T) -> Option<U> {
    NumCast::from(n)
}

/// An interface for casting between machine scalars.
pub trait NumCast: Sized + ToPrimitive {
    /// Creates a number from another value that can be converted into
    /// a primitive via the `ToPrimitive` trait. If the source value cannot be
    /// represented by the target type, then `None` is returned.
    ///
    /// A value can be represented by the target type when it lies within
    /// the range of scalars supported by the target type.
    /// For example, a negative integer cannot be represented by an unsigned
    /// integer type, and an `i64` with a very high magnitude might not be
    /// convertible to an `i32`.
    /// On the other hand, conversions with possible precision loss or truncation
    /// are admitted, like an `f32` with a decimal part to an integer type, or
    /// even a large `f64` saturating to `f32` infinity.
    fn from<T: ToPrimitive>(n: T) -> Option<Self>;
}

macro_rules! impl_num_cast {
    ($T:ty, $conv:ident) => {
        impl NumCast for $T {
            #[inline]
            #[allow(deprecated)]
            fn from<N: ToPrimitive>(n: N) -> Option<$T> {
                // `$conv` could be generated using `concat_idents!`, but that
                // macro seems to be broken at the moment
                n.$conv()
            }
        }
    };
}

impl_num_cast!(u8, to_u8);
impl_num_cast!(u16, to_u16);
impl_num_cast!(u32, to_u32);
impl_num_cast!(u64, to_u64);
#[cfg(has_i128)]
impl_num_cast!(u128, to_u128);
impl_num_cast!(usize, to_usize);
impl_num_cast!(i8, to_i8);
impl_num_cast!(i16, to_i16);
impl_num_cast!(i32, to_i32);
impl_num_cast!(i64, to_i64);
#[cfg(has_i128)]
impl_num_cast!(i128, to_i128);
impl_num_cast!(isize, to_isize);
impl_num_cast!(f32, to_f32);
impl_num_cast!(f64, to_f64);

impl<T: NumCast> NumCast for Wrapping<T> {
    fn from<U: ToPrimitive>(n: U) -> Option<Self> {
        T::from(n).map(Wrapping)
    }
}

/// A generic interface for casting between machine scalars with the
/// `as` operator, which admits narrowing and precision loss.
/// Implementers of this trait `AsPrimitive` should behave like a primitive
/// numeric type (e.g. a newtype around another primitive), and the
/// intended conversion must never fail.
///
/// # Examples
///
/// ```
/// # use num_traits::AsPrimitive;
/// let three: i32 = (3.14159265f32).as_();
/// assert_eq!(three, 3);
/// ```
///
/// # Safety
///
/// **In Rust versions before 1.45.0**, some uses of the `as` operator were not entirely safe.
/// In particular, it was undefined behavior if
/// a truncated floating point value could not fit in the target integer
/// type ([#10184](https://github.com/rust-lang/rust/issues/10184)).
///
/// ```ignore
/// # use num_traits::AsPrimitive;
/// let x: u8 = (1.04E+17).as_(); // UB
/// ```
///
pub trait AsPrimitive<T>: 'static + Copy
where
    T: 'static + Copy,
{
    /// Convert a value to another, using the `as` operator.
    fn as_(self) -> T;
}

macro_rules! impl_as_primitive {
    (@ $T: ty => $(#[$cfg:meta])* impl $U: ty ) => {
        $(#[$cfg])*
        impl AsPrimitive<$U> for $T {
            #[inline] fn as_(self) -> $U { self as $U }
        }
    };
    (@ $T: ty => { $( $U: ty ),* } ) => {$(
        impl_as_primitive!(@ $T => impl $U);
    )*};
    ($T: ty => { $( $U: ty ),* } ) => {
        impl_as_primitive!(@ $T => { $( $U ),* });
        impl_as_primitive!(@ $T => { u8, u16, u32, u64, usize });
        impl_as_primitive!(@ $T => #[cfg(has_i128)] impl u128);
        impl_as_primitive!(@ $T => { i8, i16, i32, i64, isize });
        impl_as_primitive!(@ $T => #[cfg(has_i128)] impl i128);
    };
}

impl_as_primitive!(u8 => { char, f32, f64 });
impl_as_primitive!(i8 => { f32, f64 });
impl_as_primitive!(u16 => { f32, f64 });
impl_as_primitive!(i16 => { f32, f64 });
impl_as_primitive!(u32 => { f32, f64 });
impl_as_primitive!(i32 => { f32, f64 });
impl_as_primitive!(u64 => { f32, f64 });
impl_as_primitive!(i64 => { f32, f64 });
#[cfg(has_i128)]
impl_as_primitive!(u128 => { f32, f64 });
#[cfg(has_i128)]
impl_as_primitive!(i128 => { f32, f64 });
impl_as_primitive!(usize => { f32, f64 });
impl_as_primitive!(isize => { f32, f64 });
impl_as_primitive!(f32 => { f32, f64 });
impl_as_primitive!(f64 => { f32, f64 });
impl_as_primitive!(char => { char });
impl_as_primitive!(bool => {});
#[cfg(test)]
mod tests_rug_1 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 0x14; // Concrete implementation of T that satisfies NumCast

        crate::cast::cast::<u8, f32>(p0);
    }
}#[cfg(test)]
mod tests_rug_2 {
    use super::*;
    use core::num::Wrapping;
    
    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        crate::cast::ToPrimitive::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_3 {
    use super::*;
    use core::num::Wrapping;
    
    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42); // create the local variable p0 with type core::num::Wrapping

        crate::cast::ToPrimitive::to_i8(&p0);
    }
}#[cfg(test)]
mod tests_rug_4 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        assert_eq!(crate::cast::ToPrimitive::to_i16(&p0), Some(42));
    }

    #[test]
    fn test_rug_out_of_range() {
        let mut p0: Wrapping<i32> = Wrapping(i32::MAX);

        assert_eq!(crate::cast::ToPrimitive::to_i16(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_5 {
    use super::*;
    use core::num::Wrapping;
    
    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        crate::cast::ToPrimitive::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_6 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        assert_eq!(crate::cast::ToPrimitive::to_i128(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_7 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping(42);

        assert_eq!(p0.to_usize(), Some(42));
        
        let p1: Wrapping<i64> = Wrapping(-1);
        assert_eq!(p1.to_usize(), None);

        let p2: Wrapping<usize> = Wrapping(usize::MAX);
        assert_eq!(p2.to_usize(), Some(usize::MAX));

        let p3: Wrapping<u8> = Wrapping(0);
        assert_eq!(p3.to_usize(), Some(0));
    }
}#[cfg(test)]
mod tests_rug_8 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42);

        assert_eq!(crate::cast::ToPrimitive::to_u8(&p0), Some(42));
        
        p0 = Wrapping(256);
        assert_eq!(crate::cast::ToPrimitive::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_9 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        assert_eq!(crate::cast::ToPrimitive::to_u16(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_10 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping(42);

        assert_eq!(crate::cast::ToPrimitive::to_u32(&p0), Some(42));
        
        // Test with a value that exceeds u32 max to ensure it returns None
        let p1: Wrapping<u64> = Wrapping(u64::MAX);
        assert_eq!(crate::cast::ToPrimitive::to_u32(&p1), None);
    }
}#[cfg(test)]
mod tests_rug_11 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u64> = Wrapping(42);

        assert_eq!(crate::cast::ToPrimitive::to_u128(&p0), Some(42u128));
    }
}#[cfg(test)]
mod tests_rug_12 {
    use super::*;
    use core::num::Wrapping;
    
    #[test]
    fn test_rug() {
        let mut p0: Wrapping<i32> = Wrapping(42);

        crate::cast::ToPrimitive::to_f32(&p0);
    }
}#[cfg(test)]
mod tests_rug_13 {
    use super::*;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<i32> = Wrapping(42);

        assert_eq!(crate::cast::ToPrimitive::to_f64(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_14 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 42;

        let result: Option<i32> = FromPrimitive::from_isize(p0);
        assert_eq!(result, Some(42));

        let p1: isize = -42;
        let result: Option<u32> = FromPrimitive::from_isize(p1);
        assert_eq!(result, None);

        let p2: isize = 1_000_000_000_000;
        let result: Option<i64> = FromPrimitive::from_isize(p2);
        assert_eq!(result, Some(1_000_000_000_000));

        let p3: isize = 1_000_000_000_000;
        let result: Option<i32> = FromPrimitive::from_isize(p3);
        assert_eq!(result, None);
    }
}#[cfg(test)]
mod tests_rug_15 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 127;

        let result: Option<i8> = FromPrimitive::from_i8(p0);
        assert_eq!(result, Some(127));
    }
}#[cfg(test)]
mod tests_rug_16 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_from_i16() {
        let mut p0: i16 = 12345;

        assert_eq!(FromPrimitive::from_i16(p0), Some(12345));
        
        p0 = -12345;
        assert_eq!(FromPrimitive::from_i16(p0), Some(-12345));

        p0 = 32767; // i16 max
        assert_eq!(FromPrimitive::from_i16(p0), Some(32767));

        p0 = -32768; // i16 min
        assert_eq!(FromPrimitive::from_i16(p0), Some(-32768));
    }
}#[cfg(test)]
mod tests_rug_17 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 123;

        assert_eq!(FromPrimitive::from_i32(p0), Some(123));

        let p0: i32 = -456;
        assert_eq!(FromPrimitive::from_i32(p0), Some(-456));

        // Test edge cases
        let p0: i32 = std::i32::MIN;
        assert_eq!(FromPrimitive::from_i32(p0), Some(std::i32::MIN as i32));

        let p0: i32 = std::i32::MAX;
        assert_eq!(FromPrimitive::from_i32(p0), Some(std::i32::MAX as i32));
    }
}#[cfg(test)]
mod tests_rug_18 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 9223372036854775807; // Sample data for i128

        let result: Option<i64> = FromPrimitive::from_i128(p0);

        assert_eq!(result, Some(9223372036854775807));
    }

    #[test]
    fn test_rug_out_of_range() {
        let p0: i128 = 9223372036854775808; // Out of range for i64

        let result: Option<i64> = FromPrimitive::from_i128(p0);

        assert_eq!(result, None);
    }
}#[cfg(test)]
mod tests_rug_19 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 12345;

        assert_eq!(FromPrimitive::from_usize(p0), Some(12345));
    }
}#[cfg(test)]
mod tests_rug_20 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        assert_eq!(<i32 as FromPrimitive>::from_u8(p0), Some(42));
        assert_eq!(<u32 as FromPrimitive>::from_u8(p0), Some(42));
        assert_eq!(<isize as FromPrimitive>::from_u8(p0), Some(42));
        assert_eq!(<usize as FromPrimitive>::from_u8(p0), Some(42));
        assert_eq!(<i64 as FromPrimitive>::from_u8(p0), Some(42));
        assert_eq!(<u64 as FromPrimitive>::from_u8(p0), Some(42));
        assert_eq!(<f32 as FromPrimitive>::from_u8(p0), Some(42.0));
        assert_eq!(<f64 as FromPrimitive>::from_u8(p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_21 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42u16;

        let result: Option<i32> = FromPrimitive::from_u16(p0);
        assert_eq!(result, Some(42));
    }
}#[cfg(test)]
mod tests_rug_22 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42u32;

        let _result: Option<i32> = FromPrimitive::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_23 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;
        
        <i32 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_24 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        assert_eq!(i32::from_f32(p0), Some(123));
        assert_eq!(u32::from_f32(p0), Some(123));
        assert_eq!(f64::from_f32(p0), Some(123.456));
        assert_eq!(isize::from_f32(p0), Some(123));
        assert_eq!(usize::from_f32(p0), Some(123));
    }
}#[cfg(test)]
mod tests_rug_25 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.45;

        assert_eq!(<i32 as FromPrimitive>::from_f64(p0), Some(123));
        assert_eq!(<u32 as FromPrimitive>::from_f64(p0), Some(123));
        assert_eq!(<f32 as FromPrimitive>::from_f64(p0), Some(123.45));
        assert_eq!(<i8 as FromPrimitive>::from_f64(p0), None);
        assert_eq!(<u8 as FromPrimitive>::from_f64(p0), None);
    }
}#[cfg(test)]
mod tests_rug_26 {
    use super::*;
    use crate::ToPrimitive;
    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        assert_eq!(<isize as ToPrimitive>::to_isize(&p0), Some(42));
        
        // Additional test cases
        let p1: isize = isize::MIN;
        assert_eq!(<isize as ToPrimitive>::to_isize(&p1), Some(isize::MIN));

        let p2: isize = isize::MAX;
        assert_eq!(<isize as ToPrimitive>::to_isize(&p2), Some(isize::MAX));
    }
}#[cfg(test)]
mod tests_rug_27 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 123;

        <isize as ToPrimitive>::to_i8(&p0);
    }
}#[cfg(test)]
mod tests_rug_28 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 12345;

        assert_eq!(<isize as ToPrimitive>::to_i16(&p0), Some(12345));
        
        let p0: isize = -12345;
        assert_eq!(<isize as ToPrimitive>::to_i16(&p0), Some(-12345));

        let p0: isize = i16::MAX as isize + 1;
        assert_eq!(<isize as ToPrimitive>::to_i16(&p0), None);

        let p0: isize = i16::MIN as isize - 1;
        assert_eq!(<isize as ToPrimitive>::to_i16(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_29 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 123456;

        assert_eq!(<isize as ToPrimitive>::to_i32(&p0), Some(123456));
        
        let p1: isize = -123456;
        
        assert_eq!(<isize as ToPrimitive>::to_i32(&p1), Some(-123456));
        
        let p2: isize = i32::MAX as isize + 1;
        
        assert_eq!(<isize as ToPrimitive>::to_i32(&p2), None);
        
        let p3: isize = i32::MIN as isize - 1;
        
        assert_eq!(<isize as ToPrimitive>::to_i32(&p3), None);
    }
}#[cfg(test)]
mod tests_rug_30 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456;

        assert_eq!(<isize as ToPrimitive>::to_i64(&p0), Some(123456));
        
        p0 = -789;
        assert_eq!(<isize as ToPrimitive>::to_i64(&p0), Some(-789));

        // Test edge cases
        p0 = isize::MIN;
        assert_eq!(<isize as ToPrimitive>::to_i64(&p0), Some(isize::MIN as i64));

        p0 = isize::MAX;
        assert_eq!(<isize as ToPrimitive>::to_i64(&p0), Some(isize::MAX as i64));
    }
}#[cfg(test)]
mod tests_rug_31 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789;

        assert_eq!(<isize as ToPrimitive>::to_i128(&p0), Some(123456789i128));
        
        // Test with a value that is out of range for i128 (though isize should always be within i128's range)
        let p1: isize = isize::MAX;
        assert_eq!(<isize as ToPrimitive>::to_i128(&p1), Some(isize::MAX as i128));
        
        // Test with a negative value
        let p2: isize = -987654321;
        assert_eq!(<isize as ToPrimitive>::to_i128(&p2), Some(-987654321i128));
    }
}#[cfg(test)]
mod tests_rug_32 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        assert_eq!(<isize as ToPrimitive>::to_usize(&p0), Some(42));
        
        // Test with a negative value
        p0 = -1;
        assert_eq!(<isize as ToPrimitive>::to_usize(&p0), None);
        
        // Test with a value that is out of range for usize (assuming isize is larger than usize)
        p0 = isize::MAX;
        assert_eq!(<isize as ToPrimitive>::to_usize(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_33 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 127; // Sample value for isize

        assert_eq!(<isize as ToPrimitive>::to_u8(&p0), Some(127));
        
        p0 = -1;
        assert_eq!(<isize as ToPrimitive>::to_u8(&p0), None);
        
        p0 = 256;
        assert_eq!(<isize as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_34 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 12345;

        assert_eq!(<isize as ToPrimitive>::to_u16(&p0), Some(12345));
        
        let p1: isize = -1;
        assert_eq!(<isize as ToPrimitive>::to_u16(&p1), None);

        let p2: isize = 65535;
        assert_eq!(<isize as ToPrimitive>::to_u16(&p2), Some(65535));

        let p3: isize = 65536;
        assert_eq!(<isize as ToPrimitive>::to_u16(&p3), None);
    }
}#[cfg(test)]
mod tests_rug_35 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        assert_eq!(<isize as ToPrimitive>::to_u32(&p0), Some(12345));
        
        p0 = -1;
        assert_eq!(<isize as ToPrimitive>::to_u32(&p0), None);
        
        p0 = isize::MAX;
        assert_eq!(<isize as ToPrimitive>::to_u32(&p0), if isize::MAX <= u32::MAX as isize { Some(isize::MAX as u32) } else { None });
    }
}#[cfg(test)]
mod tests_rug_36 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 12345;

        assert_eq!(<isize as ToPrimitive>::to_u64(&p0), Some(12345));
        
        let p1: isize = -1;
        assert_eq!(<isize as ToPrimitive>::to_u64(&p1), None);
        
        let p2: isize = isize::MAX;
        assert_eq!(<isize as ToPrimitive>::to_u64(&p2), Some(isize::MAX as u64));
    }
}#[cfg(test)]
mod tests_rug_37 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        assert_eq!(<isize as ToPrimitive>::to_u128(&p0), Some(12345u128));
        
        // Test with a negative number
        p0 = -1;
        assert_eq!(<isize as ToPrimitive>::to_u128(&p0), None);
        
        // Test with the maximum isize value
        p0 = isize::MAX;
        assert_eq!(<isize as ToPrimitive>::to_u128(&p0), Some(isize::MAX as u128));
        
        // Test with zero
        p0 = 0;
        assert_eq!(<isize as ToPrimitive>::to_u128(&p0), Some(0u128));
    }
}#[cfg(test)]
mod tests_rug_38 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789;

        assert_eq!(<isize as ToPrimitive>::to_f32(&p0), Some(123456789.0f32));
    }
}#[cfg(test)]
mod tests_rug_39 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        assert_eq!(<isize as ToPrimitive>::to_f64(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_40 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        assert_eq!(<i8 as ToPrimitive>::to_isize(&p0), Some(42isize));
        
        // Test edge cases
        let min_i8: i8 = i8::MIN;
        let max_i8: i8 = i8::MAX;
        
        assert_eq!(<i8 as ToPrimitive>::to_isize(&min_i8), Some(min_i8 as isize));
        assert_eq!(<i8 as ToPrimitive>::to_isize(&max_i8), Some(max_i8 as isize));
    }
}#[cfg(test)]
mod tests_rug_41 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 42;

        assert_eq!(<i8 as ToPrimitive>::to_i8(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_42 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 127;

        assert_eq!(<i8 as ToPrimitive>::to_i16(&p0), Some(127));
        
        let p0: i8 = -128;
        assert_eq!(<i8 as ToPrimitive>::to_i16(&p0), Some(-128));
        
        // Edge case within the range
        let p0: i8 = 0;
        assert_eq!(<i8 as ToPrimitive>::to_i16(&p0), Some(0));
    }
}#[cfg(test)]
mod tests_rug_43 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 127; // Sample data

        <i8 as ToPrimitive>::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_44 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 127; // Sample data for i8

        <i8 as ToPrimitive>::to_i64(&p0);
    }
}#[cfg(test)]
mod tests_rug_45 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127;

        assert_eq!(<i8 as ToPrimitive>::to_i128(&p0), Some(127));
    }
}#[cfg(test)]
mod tests_rug_46 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 123; // Sample data for i8

        assert_eq!(<i8 as ToPrimitive>::to_usize(&p0), Some(123));
        
        let p1: i8 = -1; // Negative sample
        assert_eq!(<i8 as ToPrimitive>::to_usize(&p1), None);
        
        let p2: i8 = 0; // Zero sample
        assert_eq!(<i8 as ToPrimitive>::to_usize(&p2), Some(0));
    }
}#[cfg(test)]
mod tests_rug_47 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 123;

        assert_eq!(<i8 as ToPrimitive>::to_u8(&p0), Some(123u8));

        p0 = -1;
        assert_eq!(<i8 as ToPrimitive>::to_u8(&p0), None);

        p0 = i8::MAX;
        assert_eq!(<i8 as ToPrimitive>::to_u8(&p0), Some(i8::MAX as u8));

        p0 = i8::MIN;
        assert_eq!(<i8 as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_48 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 127;

        assert_eq!(<i8 as ToPrimitive>::to_u16(&p0), Some(127u16));
    }

    #[test]
    fn test_rug_negative() {
        let p0: i8 = -1;

        assert_eq!(<i8 as ToPrimitive>::to_u16(&p0), None);
    }

    #[test]
    fn test_rug_zero() {
        let p0: i8 = 0;

        assert_eq!(<i8 as ToPrimitive>::to_u16(&p0), Some(0u16));
    }
}#[cfg(test)]
mod tests_rug_49 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = -123;

        assert_eq!(<i8 as ToPrimitive>::to_u32(&p0), None);
        
        let p1: i8 = 0;
        assert_eq!(<i8 as ToPrimitive>::to_u32(&p1), Some(0));
        
        let p2: i8 = 127;
        assert_eq!(<i8 as ToPrimitive>::to_u32(&p2), Some(127));
    }
}#[cfg(test)]
mod tests_rug_50 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = -123;

        assert_eq!(<i8 as ToPrimitive>::to_u64(&p0), None);

        p0 = 0;
        assert_eq!(<i8 as ToPrimitive>::to_u64(&p0), Some(0));

        p0 = 127;
        assert_eq!(<i8 as ToPrimitive>::to_u64(&p0), Some(127));
    }
}#[cfg(test)]
mod tests_rug_51 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 127; // Example value for i8

        assert_eq!(<i8 as ToPrimitive>::to_u128(&p0), Some(127u128));
        
        p0 = -1;
        assert_eq!(<i8 as ToPrimitive>::to_u128(&p0), None);
        
        p0 = 0;
        assert_eq!(<i8 as ToPrimitive>::to_u128(&p0), Some(0u128));
    }
}#[cfg(test)]
mod tests_rug_52 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for i8

        assert_eq!(<i8 as ToPrimitive>::to_f32(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_53 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        assert_eq!(<i8 as ToPrimitive>::to_f64(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_54 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 32767; // Sample data for i16

        assert_eq!(<i16 as ToPrimitive>::to_isize(&p0), Some(32767));
        
        let p1: i16 = -32768; // Another sample data for i16
        assert_eq!(<i16 as ToPrimitive>::to_isize(&p1), Some(-32768));

        let p2: i16 = 0; // Edge case sample data for i16
        assert_eq!(<i16 as ToPrimitive>::to_isize(&p2), Some(0));
    }
}#[cfg(test)]
mod tests_rug_55 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 123_i16;

        assert_eq!(<i16 as ToPrimitive>::to_i8(&p0), Some(123_i8));
        
        // Test with a value that fits within i8 range
        p0 = 127_i16;
        assert_eq!(<i16 as ToPrimitive>::to_i8(&p0), Some(127_i8));

        // Test with a value that exceeds i8 range
        p0 = 128_i16;
        assert_eq!(<i16 as ToPrimitive>::to_i8(&p0), None);

        // Test with the minimum value of i16 that fits within i8 range
        p0 = -128_i16;
        assert_eq!(<i16 as ToPrimitive>::to_i8(&p0), Some(-128_i8));

        // Test with a value below i8 range
        p0 = -129_i16;
        assert_eq!(<i16 as ToPrimitive>::to_i8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_56 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42_i16;

        <i16 as ToPrimitive>::to_i16(&p0);
    }
}#[cfg(test)]
mod tests_rug_57 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Sample data for i16

        <i16 as ToPrimitive>::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_58 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 32767; // Sample data for i16

        <i16 as ToPrimitive>::to_i64(&p0);
        
        assert_eq!(<i16 as ToPrimitive>::to_i64(&p0), Some(32767));
    }
}#[cfg(test)]
mod tests_rug_59 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 12345;

        assert_eq!(<i16 as ToPrimitive>::to_i128(&p0), Some(12345));
    }
}#[cfg(test)]
mod tests_rug_60 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 123;

        assert_eq!(<i16 as ToPrimitive>::to_usize(&p0), Some(123));
        
        let p0: i16 = -1;
        assert_eq!(<i16 as ToPrimitive>::to_usize(&p0), None);
        
        let p0: i16 = 32767;
        assert_eq!(<i16 as ToPrimitive>::to_usize(&p0), Some(32767));
    }
}#[cfg(test)]
mod tests_rug_61 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 127; // Sample data for i16

        assert_eq!(<i16 as ToPrimitive>::to_u8(&p0), Some(127));
        
        p0 = -1;
        assert_eq!(<i16 as ToPrimitive>::to_u8(&p0), None);
        
        p0 = 256;
        assert_eq!(<i16 as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_62 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 32767;

        <i16 as ToPrimitive>::to_u16(&p0);
    }
}#[cfg(test)]
mod tests_rug_63 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 12345; // Sample data for i16

        assert_eq!(<i16 as ToPrimitive>::to_u32(&p0), Some(12345u32));
        
        let p0_negative: i16 = -1;
        assert_eq!(<i16 as ToPrimitive>::to_u32(&p0_negative), None);
        
        let p0_max: i16 = i16::MAX;
        assert_eq!(<i16 as ToPrimitive>::to_u32(&p0_max), Some(32767u32));
    }
}#[cfg(test)]
mod tests_rug_64 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = -32768; // Example sample data for i16

        assert_eq!(<i16 as ToPrimitive>::to_u64(&p0), None);
        
        let p1: i16 = 0;
        assert_eq!(<i16 as ToPrimitive>::to_u64(&p1), Some(0));

        let p2: i16 = 32767;
        assert_eq!(<i16 as ToPrimitive>::to_u64(&p2), Some(32767));
        
        let p3: i16 = 100;
        assert_eq!(<i16 as ToPrimitive>::to_u64(&p3), Some(100));
    }
}#[cfg(test)]
mod tests_rug_65 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 32767; // Sample data for i16

        let result = <i16 as ToPrimitive>::to_u128(&p0);

        assert_eq!(result, Some(32767u128));
    }

    #[test]
    fn test_rug_negative() {
        let p0: i16 = -1; // Sample data for i16

        let result = <i16 as ToPrimitive>::to_u128(&p0);

        assert_eq!(result, None);
    }

    #[test]
    fn test_rug_zero() {
        let p0: i16 = 0; // Sample data for i16

        let result = <i16 as ToPrimitive>::to_u128(&p0);

        assert_eq!(result, Some(0u128));
    }
}#[cfg(test)]
mod tests_rug_66 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767;

        assert_eq!(<i16 as ToPrimitive>::to_f32(&p0), Some(32767.0));
    }
}#[cfg(test)]
mod tests_rug_67 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        assert_eq!(<i16 as ToPrimitive>::to_f64(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_68 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 12345;

        <i32 as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_69 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 127; // Sample data within the range of i8

        assert_eq!(<i32 as ToPrimitive>::to_i8(&p0), Some(127));
        
        let p1: i32 = -128; // Boundary value
        assert_eq!(<i32 as ToPrimitive>::to_i8(&p1), Some(-128));

        let p2: i32 = 128; // Out of range for i8
        assert_eq!(<i32 as ToPrimitive>::to_i8(&p2), None);

        let p3: i32 = -129; // Out of range for i8
        assert_eq!(<i32 as ToPrimitive>::to_i8(&p3), None);
    }
}#[cfg(test)]
mod tests_rug_70 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let p0: i32 = 123;

        assert_eq!(<i32 as ToPrimitive>::to_i16(&p0), Some(123));
        
        let p1: i32 = -456;
        assert_eq!(<i32 as ToPrimitive>::to_i16(&p1), Some(-456));
        
        let p2: i32 = i16::MAX as i32 + 1;
        assert_eq!(<i32 as ToPrimitive>::to_i16(&p2), None);
        
        let p3: i32 = i16::MIN as i32 - 1;
        assert_eq!(<i32 as ToPrimitive>::to_i16(&p3), None);
    }
}#[cfg(test)]
mod tests_rug_71 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42;

        <i32 as ToPrimitive>::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_72 {
    use super::*;
    use crate::ToPrimitive;
    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as ToPrimitive>::to_i64(&p0);
    }
}#[cfg(test)]
mod tests_rug_73 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        <i32 as ToPrimitive>::to_i128(&p0);
    }
}#[cfg(test)]
mod tests_rug_74 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42; // Sample data for i32

        assert_eq!(<i32 as ToPrimitive>::to_usize(&p0), Some(42));
        
        let p1: i32 = -1;
        assert_eq!(<i32 as ToPrimitive>::to_usize(&p1), None);
        
        let p2: i32 = std::usize::MAX as i32 + 1;
        assert_eq!(<i32 as ToPrimitive>::to_usize(&p2), None);
    }
}#[cfg(test)]
mod tests_rug_75 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let p0: i32 = 10;

        assert_eq!(<i32 as ToPrimitive>::to_u8(&p0), Some(10));
        
        let p1: i32 = -5;
        assert_eq!(<i32 as ToPrimitive>::to_u8(&p1), None);
        
        let p2: i32 = 256;
        assert_eq!(<i32 as ToPrimitive>::to_u8(&p2), None);
    }
}#[cfg(test)]
mod tests_rug_76 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10; // Sample data for i32

        assert_eq!(<i32 as ToPrimitive>::to_u16(&p0), Some(10));
        
        p0 = -5;
        assert_eq!(<i32 as ToPrimitive>::to_u16(&p0), None);
        
        p0 = 65535;
        assert_eq!(<i32 as ToPrimitive>::to_u16(&p0), Some(65535));
        
        p0 = 65536;
        assert_eq!(<i32 as ToPrimitive>::to_u16(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_77 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42; // Sample data for i32

        assert_eq!(<i32 as ToPrimitive>::to_u32(&p0), Some(42u32));
        
        let p1: i32 = -42; // Negative sample data for i32
        assert_eq!(<i32 as ToPrimitive>::to_u32(&p1), None);

        let p2: i32 = std::i32::MAX; // Max value for i32
        assert_eq!(<i32 as ToPrimitive>::to_u32(&p2), Some(2147483647u32));

        let p3: i32 = std::i32::MIN; // Min value for i32
        assert_eq!(<i32 as ToPrimitive>::to_u32(&p3), None);
    }
}#[cfg(test)]
mod tests_rug_78 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        assert_eq!(<i32 as ToPrimitive>::to_u64(&p0), Some(42));
    }

    #[test]
    fn test_negative_value() {
        let mut p0: i32 = -1;

        assert_eq!(<i32 as ToPrimitive>::to_u64(&p0), None);
    }

    #[test]
    fn test_max_i32() {
        let mut p0: i32 = i32::MAX;

        assert_eq!(<i32 as ToPrimitive>::to_u64(&p0), Some(i32::MAX as u64));
    }
}#[cfg(test)]
mod tests_rug_79 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 12345;

        <i32 as ToPrimitive>::to_u128(&p0);
    }
}#[cfg(test)]
mod tests_rug_80 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42; // Sample data for i32

        assert_eq!(<i32 as ToPrimitive>::to_f32(&p0), Some(42.0f32));
    }
}#[cfg(test)]
mod tests_rug_81 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42; // Sample data for i32

        assert_eq!(<i32 as ToPrimitive>::to_f64(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_82 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789012345;

        <i64 as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_83 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 127;

        assert_eq!(<i64 as ToPrimitive>::to_i8(&p0), Some(127));

        let p1: i64 = 128;
        assert_eq!(<i64 as ToPrimitive>::to_i8(&p1), None);

        let p2: i64 = -129;
        assert_eq!(<i64 as ToPrimitive>::to_i8(&p2), None);

        let p3: i64 = 0;
        assert_eq!(<i64 as ToPrimitive>::to_i8(&p3), Some(0));

        let p4: i64 = -128;
        assert_eq!(<i64 as ToPrimitive>::to_i8(&p4), Some(-128));
    }
}#[cfg(test)]
mod tests_rug_84 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 12345;

        <i64 as ToPrimitive>::to_i16(&p0);
    }
}#[cfg(test)]
mod tests_rug_85 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        assert_eq!(p0.to_i32(), Some(12345));

        let p1: i64 = -12345;
        assert_eq!(p1.to_i32(), Some(-12345));

        let p2: i64 = i64::MAX;
        assert_eq!(p2.to_i32(), None);

        let p3: i64 = i64::MIN;
        assert_eq!(p3.to_i32(), None);
    }
}#[cfg(test)]
mod tests_rug_86 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as ToPrimitive>::to_i64(&p0);
    }
}#[cfg(test)]
mod tests_rug_87 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789012345;

        assert_eq!(<i64 as ToPrimitive>::to_i128(&p0), Some(123456789012345));
        
        p0 = -987654321987654;
        assert_eq!(<i64 as ToPrimitive>::to_i128(&p0), Some(-987654321987654));

        p0 = i64::MAX;
        assert_eq!(<i64 as ToPrimitive>::to_i128(&p0), Some(i64::MAX as i128));

        p0 = i64::MIN;
        assert_eq!(<i64 as ToPrimitive>::to_i128(&p0), Some(i64::MIN as i128));
    }
}#[cfg(test)]
mod tests_rug_88 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: i64 = 123;

        <i64 as ToPrimitive>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_89 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123; // Sample data for i64

        assert_eq!(<i64 as ToPrimitive>::to_u8(&p0), Some(123));
        
        let p1: i64 = -1;
        assert_eq!(<i64 as ToPrimitive>::to_u8(&p1), None);
        
        let p2: i64 = 256;
        assert_eq!(<i64 as ToPrimitive>::to_u8(&p2), None);
    }
}#[cfg(test)]
mod tests_rug_90 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 123;

        <i64 as ToPrimitive>::to_u16(&p0);
    }
}#[cfg(test)]
mod tests_rug_91 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        assert_eq!(<i64 as ToPrimitive>::to_u32(&p0), Some(12345));
        
        p0 = -1;
        assert_eq!(<i64 as ToPrimitive>::to_u32(&p0), None);
        
        p0 = 4294967295; // u32::MAX
        assert_eq!(<i64 as ToPrimitive>::to_u32(&p0), Some(4294967295));
        
        p0 = 4294967296; // u32::MAX + 1
        assert_eq!(<i64 as ToPrimitive>::to_u32(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_92 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_93 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        assert_eq!(<i64 as ToPrimitive>::to_u128(&p0), Some(12345u128));

        p0 = -1;
        assert_eq!(<i64 as ToPrimitive>::to_u128(&p0), None);

        p0 = i64::MAX;
        assert_eq!(<i64 as ToPrimitive>::to_u128(&p0), Some(i64::MAX as u128));
    }
}#[cfg(test)]
mod tests_rug_94 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        assert_eq!(<i64 as ToPrimitive>::to_f32(&p0), Some(123456789.0f32));
    }
}#[cfg(test)]
mod tests_rug_95 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        assert_eq!(<i64 as ToPrimitive>::to_f64(&p0), Some(12345.0));
    }
}#[cfg(test)]
mod tests_rug_96 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 123456789012345678901234567890i128;

        <i128 as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_97 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 127; // Sample data within the range of i8

        assert_eq!(<i128 as ToPrimitive>::to_i8(&p0), Some(127));

        let p1: i128 = 128; // Out of the range of i8
        assert_eq!(<i128 as ToPrimitive>::to_i8(&p1), None);

        let p2: i128 = -129; // Below the range of i8
        assert_eq!(<i128 as ToPrimitive>::to_i8(&p2), None);

        let p3: i128 = 0; // Edge case within the range of i8
        assert_eq!(<i128 as ToPrimitive>::to_i8(&p3), Some(0));

        let p4: i128 = -128; // Edge case within the range of i8
        assert_eq!(<i128 as ToPrimitive>::to_i8(&p4), Some(-128));
    }
}#[cfg(test)]
mod tests_rug_98 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 32767; // Sample data within the range of i16

        <i128 as ToPrimitive>::to_i16(&p0);
    }

    #[test]
    fn test_out_of_range() {
        let p0: i128 = 32768; // Sample data out of the range of i16

        assert_eq!(<i128 as ToPrimitive>::to_i16(&p0), None);
    }

    #[test]
    fn test_min_value() {
        let p0: i128 = -32768; // Sample data at the min value of i16

        assert_eq!(<i128 as ToPrimitive>::to_i16(&p0), Some(-32768));
    }

    #[test]
    fn test_below_min_value() {
        let p0: i128 = -32769; // Sample data below the min value of i16

        assert_eq!(<i128 as ToPrimitive>::to_i16(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_99 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 123456789012345678901234567890123456789;

        assert_eq!(<i128 as ToPrimitive>::to_i32(&p0), None);

        let p1: i128 = 2147483647;
        assert_eq!(<i128 as ToPrimitive>::to_i32(&p1), Some(2147483647));

        let p2: i128 = -2147483648;
        assert_eq!(<i128 as ToPrimitive>::to_i32(&p2), Some(-2147483648));

        let p3: i128 = 2147483648;
        assert_eq!(<i128 as ToPrimitive>::to_i32(&p3), None);

        let p4: i128 = -2147483649;
        assert_eq!(<i128 as ToPrimitive>::to_i32(&p4), None);
    }
}#[cfg(test)]
mod tests_rug_100 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9_223_372_036_854_775_807_i128; // Sample data within the range of i64

        assert_eq!(<i128 as ToPrimitive>::to_i64(&p0), Some(9_223_372_036_854_775_807_i64));

        p0 = 18_446_744_073_709_551_615_i128; // Sample data out of the range of i64
        assert_eq!(<i128 as ToPrimitive>::to_i64(&p0), None);

        p0 = -9_223_372_036_854_775_809_i128; // Sample data out of the range of i64
        assert_eq!(<i128 as ToPrimitive>::to_i64(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_101 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 9223372036854775807; // Sample data for i128

        <i128 as ToPrimitive>::to_i128(&p0);
    }
}#[cfg(test)]
mod tests_rug_102 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42; // Sample data for i128

        assert_eq!(<i128 as ToPrimitive>::to_usize(&p0), Some(42));
        assert_eq!(<i128 as ToPrimitive>::to_usize(&(usize::MAX as i128 + 1)), None);
        assert_eq!(<i128 as ToPrimitive>::to_usize(&-1), None);
    }
}#[cfg(test)]
mod tests_rug_103 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 127; // Sample data within the range of u8

        assert_eq!(<i128 as ToPrimitive>::to_u8(&p0), Some(127));
        
        p0 = -1;
        assert_eq!(<i128 as ToPrimitive>::to_u8(&p0), None);
        
        p0 = 128;
        assert_eq!(<i128 as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_104 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;

        assert_eq!(<i128 as ToPrimitive>::to_u16(&p0), Some(42));
        
        p0 = -1;
        assert_eq!(<i128 as ToPrimitive>::to_u16(&p0), None);
        
        p0 = 65535;
        assert_eq!(<i128 as ToPrimitive>::to_u16(&p0), Some(65535));
        
        p0 = 65536;
        assert_eq!(<i128 as ToPrimitive>::to_u16(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_105 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 42;

        assert_eq!(<i128 as ToPrimitive>::to_u32(&p0), Some(42));
        
        let p1: i128 = -1;
        assert_eq!(<i128 as ToPrimitive>::to_u32(&p1), None);
        
        let p2: i128 = 4294967295; // u32::MAX
        assert_eq!(<i128 as ToPrimitive>::to_u32(&p2), Some(4294967295));
        
        let p3: i128 = 4294967296; // u32::MAX + 1
        assert_eq!(<i128 as ToPrimitive>::to_u32(&p3), None);
    }
}#[cfg(test)]
mod tests_rug_106 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;

        assert_eq!(<i128 as ToPrimitive>::to_u64(&p0), Some(42));
        
        // Test with a value that is out of range for u64
        let large_value: i128 = (u64::MAX as i128) + 1;
        assert_eq!(<i128 as ToPrimitive>::to_u64(&large_value), None);
        
        // Test with a negative value
        let negative_value: i128 = -1;
        assert_eq!(<i128 as ToPrimitive>::to_u64(&negative_value), None);
    }
}#[cfg(test)]
mod tests_rug_107 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789;

        assert_eq!(<i128 as ToPrimitive>::to_u128(&p0), Some(123456789012345678901234567890123456789u128));

        p0 = -1;
        assert_eq!(<i128 as ToPrimitive>::to_u128(&p0), None);

        p0 = 0;
        assert_eq!(<i128 as ToPrimitive>::to_u128(&p0), Some(0u128));

        p0 = i128::MAX;
        assert_eq!(<i128 as ToPrimitive>::to_u128(&p0), None);

        p0 = u128::MAX as i128;
        assert_eq!(<i128 as ToPrimitive>::to_u128(&p0), Some(u128::MAX));
    }
}#[cfg(test)]
mod tests_rug_108 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9_223_372_036_854_775_807_i128; // Sample data for i128

        assert_eq!(p0.to_f32(), Some(p0 as f32));
    }
}#[cfg(test)]
mod tests_rug_109 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128

        assert_eq!(<i128 as ToPrimitive>::to_f64(&p0), Some(9223372036854775807.0));
    }
}#[cfg(test)]
mod tests_rug_110 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        assert_eq!(p0.to_isize(), Some(12345));
        
        // Additional test cases
        let p1: usize = isize::MAX as usize;
        let p2: usize = isize::MAX as usize + 1;
        let p3: usize = 0;

        assert_eq!(p1.to_isize(), Some(isize::MAX));
        assert_eq!(p2.to_isize(), None);
        assert_eq!(p3.to_isize(), Some(0));
    }
}#[cfg(test)]
mod tests_rug_111 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 127; // Sample data for usize

        assert_eq!(p0.to_i8(), Some(127));
        
        p0 = 128;
        assert_eq!(p0.to_i8(), None);
        
        p0 = 0;
        assert_eq!(p0.to_i8(), Some(0));
        
        p0 = 255;
        assert_eq!(p0.to_i8(), None);
    }
}#[cfg(test)]
mod tests_rug_112 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 32767; // Example value for usize that fits in i16

        assert_eq!(p0.to_i16(), Some(32767));
        
        let p1: usize = 32768; // Example value for usize that does not fit in i16

        assert_eq!(p1.to_i16(), None);
    }
}#[cfg(test)]
mod tests_rug_113 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        assert_eq!(p0.to_i32(), Some(12345));
        
        // Test with a value that is larger than i32::MAX
        p0 = 1_000_000_000_000;
        assert_eq!(p0.to_i32(), None);
    }
}#[cfg(test)]
mod tests_rug_114 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42; // Sample data for usize

        <usize as ToPrimitive>::to_i64(&p0);
    }
}#[cfg(test)]
mod tests_rug_115 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42; // Sample data for usize

        let result = <usize as ToPrimitive>::to_i128(&p0);
        assert_eq!(result, Some(42));
    }
}#[cfg(test)]
mod tests_rug_116 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        assert_eq!(<usize as ToPrimitive>::to_usize(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_117 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 255;

        assert_eq!(<usize as ToPrimitive>::to_u8(&p0), Some(255));
    }

    #[test]
    fn test_rug_out_of_bounds() {
        let p0: usize = 256;

        assert_eq!(<usize as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_118 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 65535; // Sample data for usize

        <usize as ToPrimitive>::to_u16(&p0);
    }
}#[cfg(test)]
mod tests_rug_119 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42; // Sample data for usize

        assert_eq!(<usize as ToPrimitive>::to_u32(&p0), Some(42));
        
        let p1: usize = u32::MAX as usize;
        assert_eq!(<usize as ToPrimitive>::to_u32(&p1), Some(u32::MAX));

        let p2: usize = u32::MAX as usize + 1;
        assert_eq!(<usize as ToPrimitive>::to_u32(&p2), None);
    }
}#[cfg(test)]
mod tests_rug_120 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <usize as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_121 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 123456789;

        assert_eq!(<usize as ToPrimitive>::to_u128(&p0), Some(123456789));
    }
}#[cfg(test)]
mod tests_rug_122 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        assert_eq!(<usize as ToPrimitive>::to_f32(&p0), Some(12345.0));
    }
}#[cfg(test)]
mod tests_rug_123 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 123456789;

        assert_eq!(<usize as ToPrimitive>::to_f64(&p0), Some(p0 as f64));
    }
}#[cfg(test)]
mod tests_rug_124 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 123;

        assert_eq!(<u8 as ToPrimitive>::to_isize(&p0), Some(123));
    }
}#[cfg(test)]
mod tests_rug_125 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 127;

        assert_eq!(<u8 as ToPrimitive>::to_i8(&p0), Some(127));
        
        let p1: u8 = 255;
        assert_eq!(<u8 as ToPrimitive>::to_i8(&p1), None);
    }
}#[cfg(test)]
mod tests_rug_126 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 123;

        assert_eq!(<u8 as ToPrimitive>::to_i16(&p0), Some(123));
        
        // Test edge case where the value is within the range of i16
        p0 = 0;
        assert_eq!(<u8 as ToPrimitive>::to_i16(&p0), Some(0));

        // Test another boundary case
        p0 = 255;
        assert_eq!(<u8 as ToPrimitive>::to_i16(&p0), Some(255));
    }
}#[cfg(test)]
mod tests_rug_127 {
    use super::*;
    use crate::ToPrimitive;
    #[test]
    fn test_rug() {
        let p0: u8 = 123;

        <u8 as ToPrimitive>::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_128 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        assert_eq!(<u8 as ToPrimitive>::to_i64(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_129 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; // Sample data for u8

        <u8 as ToPrimitive>::to_i128(&p0);
    }
}#[cfg(test)]
mod tests_rug_130 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; // Sample data for u8

        assert_eq!(<u8 as ToPrimitive>::to_usize(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_131 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        <u8 as ToPrimitive>::to_u8(&p0);
    }
}#[cfg(test)]
mod tests_rug_132 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 255;

        <u8 as ToPrimitive>::to_u16(&p0);
    }
}#[cfg(test)]
mod tests_rug_133 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        assert_eq!(<u8 as ToPrimitive>::to_u32(&p0), Some(42));
        
        // Testing edge cases
        let max_u8: u8 = 255;
        assert_eq!(<u8 as ToPrimitive>::to_u32(&max_u8), Some(255));

        let zero_u8: u8 = 0;
        assert_eq!(<u8 as ToPrimitive>::to_u32(&zero_u8), Some(0));
    }
}#[cfg(test)]
mod tests_rug_134 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; // Sample data for u8

        <u8 as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_135 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42; // Sample data for u8

        assert_eq!(<u8 as ToPrimitive>::to_u128(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_136 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        assert_eq!(<u8 as ToPrimitive>::to_f32(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_137 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        assert_eq!(<u8 as ToPrimitive>::to_f64(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_138 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        assert_eq!(<u16 as ToPrimitive>::to_isize(&p0), Some(42));
        
        p0 = 32768;
        assert_eq!(<u16 as ToPrimitive>::to_isize(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_139 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 123; // Sample data for u16

        assert_eq!(p0.to_i8(), Some(123));
        let p0_out_of_range: u16 = 300; // Out of i8 range sample
        assert_eq!(p0_out_of_range.to_i8(), None);
    }
}#[cfg(test)]
mod tests_rug_140 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 300u16;

        <u16 as ToPrimitive>::to_i16(&p0);
    }
}#[cfg(test)]
mod tests_rug_141 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 12345u16;

        <u16 as ToPrimitive>::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_142 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42;

        assert_eq!(<u16 as ToPrimitive>::to_i64(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_143 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 12345;
        
        assert_eq!(<u16 as ToPrimitive>::to_i128(&p0), Some(12345));
    }
}#[cfg(test)]
mod tests_rug_144 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        <u16 as ToPrimitive>::to_usize(&p0);
        
        assert_eq!(<u16 as ToPrimitive>::to_usize(&p0), Some(42));
        
        // Test edge case where value is within range
        let max_u16: u16 = std::u16::MAX;
        assert_eq!(<u16 as ToPrimitive>::to_usize(&max_u16), Some(max_u16 as usize));

        // No need to test out-of-range case for u16 -> usize conversion, since u16 is smaller than usize
    }
}#[cfg(test)]
mod tests_rug_145 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: u16 = 255;

        assert_eq!(<u16 as ToPrimitive>::to_u8(&p0), Some(255));
        
        p0 = 256;
        assert_eq!(<u16 as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_146 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        <u16 as ToPrimitive>::to_u16(&p0);
    }
}#[cfg(test)]
mod tests_rug_147 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42;

        assert_eq!(<u16 as ToPrimitive>::to_u32(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_148 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42;

        assert_eq!(<u16 as ToPrimitive>::to_u64(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_149 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 500; // Sample data for u16

        assert_eq!(<u16 as ToPrimitive>::to_u128(&p0), Some(500));
    }
}#[cfg(test)]
mod tests_rug_150 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42; // Sample data for u16

        assert_eq!(<u16 as ToPrimitive>::to_f32(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_151 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42;

        assert_eq!(<u16 as ToPrimitive>::to_f64(&p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_152 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let p0: u32 = 100;

        <u32 as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_153 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 100;

        <u32 as ToPrimitive>::to_i8(&p0);
    }
}#[cfg(test)]
mod tests_rug_154 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: u32 = 12345;

        <u32 as ToPrimitive>::to_i16(&p0);
    }
}#[cfg(test)]
mod tests_rug_155 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as ToPrimitive>::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_156 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as ToPrimitive>::to_i64(&p0);
    }
}#[cfg(test)]
mod tests_rug_157 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; 

        assert_eq!(p0.to_i128(), Some(42));
        
        // Test with a value that is within the range of i128
        p0 = 123456789;
        assert_eq!(p0.to_i128(), Some(123456789));

        // Test with a value that is at the max limit of u32, which should still fit in i128
        p0 = u32::MAX;
        assert_eq!(p0.to_i128(), Some(u32::MAX as i128));
    }
}#[cfg(test)]
mod tests_rug_158 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42;

        <u32 as ToPrimitive>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_159 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42;

        assert_eq!(<u32 as ToPrimitive>::to_u8(&p0), Some(42));

        let p1: u32 = 256;
        assert_eq!(<u32 as ToPrimitive>::to_u8(&p1), None);
    }
}#[cfg(test)]
mod tests_rug_160 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 65535; // Sample data within the range of u16

        assert_eq!(<u32 as ToPrimitive>::to_u16(&p0), Some(65535));

        let p1: u32 = 65536; // Sample data out of the range of u16

        assert_eq!(<u32 as ToPrimitive>::to_u16(&p1), None);
    }
}#[cfg(test)]
mod tests_rug_161 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42;

        <u32 as ToPrimitive>::to_u32(&p0);
    }
}#[cfg(test)]
mod tests_rug_162 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_163 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42;

        assert_eq!(<u32 as ToPrimitive>::to_u128(&p0), Some(42u128));
    }
}#[cfg(test)]
mod tests_rug_164 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 12345u32;

        <u32 as ToPrimitive>::to_f32(&p0);
    }
}#[cfg(test)]
mod tests_rug_165 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as ToPrimitive>::to_f64(&p0);
    }
}#[cfg(test)]
mod tests_rug_166 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        <u64 as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_167 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 123;

        assert_eq!(<u64 as ToPrimitive>::to_i8(&p0), Some(123));
    }

    #[test]
    fn test_too_large_value() {
        let p0: u64 = 500;

        assert_eq!(<u64 as ToPrimitive>::to_i8(&p0), None);
    }

    #[test]
    fn test_max_value() {
        let p0: u64 = i8::MAX as u64;

        assert_eq!(<u64 as ToPrimitive>::to_i8(&p0), Some(i8::MAX));
    }

    #[test]
    fn test_exceeds_max_value() {
        let p0: u64 = (i8::MAX as u64) + 1;

        assert_eq!(<u64 as ToPrimitive>::to_i8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_168 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let p0: u64 = 12345;

        assert_eq!(p0.to_i16(), Some(12345));
        
        let p0_max_within_range: u64 = i16::MAX as u64;
        assert_eq!(p0_max_within_range.to_i16(), Some(i16::MAX));

        let p0_out_of_range: u64 = (i16::MAX as u64) + 1;
        assert_eq!(p0_out_of_range.to_i16(), None);
    }
}#[cfg(test)]
mod tests_rug_169 {
    use super::*;
    use crate::ToPrimitive;
    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        assert_eq!(p0.to_i32(), Some(12345));
        
        let mut p0_max: u64 = i32::MAX as u64;
        assert_eq!(p0_max.to_i32(), Some(i32::MAX));

        let mut p0_overflow: u64 = (i32::MAX as u64) + 1;
        assert_eq!(p0_overflow.to_i32(), None);
    }
}#[cfg(test)]
mod tests_rug_170 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890123456789u64;

        assert_eq!(<u64 as ToPrimitive>::to_i64(&p0), Some(1234567890123456789i64));
    }
}#[cfg(test)]
mod tests_rug_171 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 1234567890;

        assert_eq!(<u64 as ToPrimitive>::to_i128(&p0), Some(1234567890));
        
        // Test with a value that is larger than i128::MAX to ensure it returns None
        let large_value: u64 = 18446744073709551615; // u64::MAX
        assert_eq!(<u64 as ToPrimitive>::to_i128(&large_value), None);
    }
}#[cfg(test)]
mod tests_rug_172 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        <u64 as ToPrimitive>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_173 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: u64 = 255;

        assert_eq!(<u64 as ToPrimitive>::to_u8(&p0), Some(255));
        
        p0 = 256;
        assert_eq!(<u64 as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_174 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        assert_eq!(<u64 as ToPrimitive>::to_u16(&p0), Some(12345));
        
        p0 = 70000;
        assert_eq!(<u64 as ToPrimitive>::to_u16(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_175 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        assert_eq!(<u64 as ToPrimitive>::to_u32(&p0), Some(12345));
        
        p0 = 4294967295; // u32::MAX
        assert_eq!(<u64 as ToPrimitive>::to_u32(&p0), Some(4294967295));

        p0 = 4294967296; // u32::MAX + 1
        assert_eq!(<u64 as ToPrimitive>::to_u32(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_176 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 18446744073709551615; // Sample data for u64

        <u64 as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_177 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789012345;

        <u64 as ToPrimitive>::to_u128(&p0);
    }
}#[cfg(test)]
mod tests_rug_178 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789012345;

        assert_eq!(<u64 as ToPrimitive>::to_f32(&p0), Some(123456789012345.0));
    }
}#[cfg(test)]
mod tests_rug_179 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;

        <u64 as ToPrimitive>::to_f64(&p0);
    }
}#[cfg(test)]
mod tests_rug_180 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        <u128 as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_181 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 127u128;

        <u128 as ToPrimitive>::to_i8(&p0);
    }
}#[cfg(test)]
mod tests_rug_182 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 32767; // Sample data within the range of i16

        assert_eq!(<u128 as ToPrimitive>::to_i16(&p0), Some(32767));
        
        p0 = 32768; // Sample data out of the range of i16
        assert_eq!(<u128 as ToPrimitive>::to_i16(&p0), None);
        
        p0 = 65535; // Another sample data out of the range of i16
        assert_eq!(<u128 as ToPrimitive>::to_i16(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_183 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42;

        assert_eq!(<u128 as ToPrimitive>::to_i32(&p0), Some(42));
        
        let p1: u128 = i32::MAX as u128;
        assert_eq!(<u128 as ToPrimitive>::to_i32(&p1), Some(i32::MAX));
        
        let p2: u128 = (i32::MAX as u128) + 1;
        assert_eq!(<u128 as ToPrimitive>::to_i32(&p2), None);
    }
}#[cfg(test)]
mod tests_rug_184 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        assert_eq!(<u128 as ToPrimitive>::to_i64(&p0), Some(42i64));

        // Test with a value larger than i64::MAX
        p0 = 9_223_372_036_854_775_808u128;
        assert_eq!(<u128 as ToPrimitive>::to_i64(&p0), None);

        // Test with i64::MAX
        p0 = 9_223_372_036_854_775_807u128;
        assert_eq!(<u128 as ToPrimitive>::to_i64(&p0), Some(9_223_372_036_854_775_807i64));
    }
}#[cfg(test)]
mod tests_rug_185 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;

        assert_eq!(<u128 as ToPrimitive>::to_i128(&p0), Some(12345678901234567890123456789012345678));
        
        p0 = u128::MAX;
        assert_eq!(<u128 as ToPrimitive>::to_i128(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_186 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42;

        <u128 as ToPrimitive>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_187 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        assert_eq!(<u128 as ToPrimitive>::to_u8(&p0), Some(42u8));
        
        let p1: u128 = 255u128;
        assert_eq!(<u128 as ToPrimitive>::to_u8(&p1), Some(255u8));

        let p2: u128 = 256u128;
        assert_eq!(<u128 as ToPrimitive>::to_u8(&p2), None);

        let p3: u128 = 0u128;
        assert_eq!(<u128 as ToPrimitive>::to_u8(&p3), Some(0u8));
    }
}#[cfg(test)]
mod tests_rug_188 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 100u128;

        assert_eq!(<u128 as ToPrimitive>::to_u16(&p0), Some(100u16));

        let p1: u128 = 65535u128;
        assert_eq!(<u128 as ToPrimitive>::to_u16(&p1), Some(65535u16));

        let p2: u128 = 65536u128;
        assert_eq!(<u128 as ToPrimitive>::to_u16(&p2), None);
    }
}#[cfg(test)]
mod tests_rug_189 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;

        assert_eq!(<u128 as ToPrimitive>::to_u32(&p0), Some(42u32));
        
        let p0_max_within_range: u128 = u32::MAX as u128;
        assert_eq!(<u128 as ToPrimitive>::to_u32(&p0_max_within_range), Some(u32::MAX));

        let p0_out_of_range: u128 = u32::MAX as u128 + 1;
        assert_eq!(<u128 as ToPrimitive>::to_u32(&p0_out_of_range), None);
    }
}#[cfg(test)]
mod tests_rug_190 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;
        
        assert_eq!(<u128 as ToPrimitive>::to_u64(&p0), Some(42u64));
    }
}#[cfg(test)]
mod tests_rug_191 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42;

        assert_eq!(<u128 as ToPrimitive>::to_u128(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_192 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615u128; // Sample data for u128

        <u128 as ToPrimitive>::to_f32(&p0);
    }
}#[cfg(test)]
mod tests_rug_193 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128

        <u128 as ToPrimitive>::to_f64(&p0);

    }
}#[cfg(test)]
mod tests_rug_194 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 42.0;

        <f32 as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_195 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 127.0; // Sample data for f32

        assert_eq!(p0.to_i8(), Some(127));
    }

    #[test]
    fn test_too_large() {
        let p0: f32 = 128.0; // Larger than i8::MAX

        assert_eq!(p0.to_i8(), None);
    }

    #[test]
    fn test_negative() {
        let p0: f32 = -128.0; // Sample data for f32

        assert_eq!(p0.to_i8(), Some(-128));
    }

    #[test]
    fn test_too_small() {
        let p0: f32 = -129.0; // Smaller than i8::MIN

        assert_eq!(p0.to_i8(), None);
    }

    #[test]
    fn test_fractional_part() {
        let p0: f32 = 127.5; // Fractional part should truncate towards zero

        assert_eq!(p0.to_i8(), Some(127));
    }
}#[cfg(test)]
mod tests_rug_196 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        assert_eq!(p0.to_i16(), Some(123));
        
        let p1: f32 = -123.456;
        assert_eq!(p1.to_i16(), Some(-123));

        let p2: f32 = 32768.0; // i16::MAX + 1
        assert_eq!(p2.to_i16(), None);

        let p3: f32 = -32769.0; // i16::MIN - 1
        assert_eq!(p3.to_i16(), None);

        let p4: f32 = 0.0;
        assert_eq!(p4.to_i16(), Some(0));

        let p5: f32 = -0.0;
        assert_eq!(p5.to_i16(), Some(0));
    }
}#[cfg(test)]
mod tests_rug_197 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        assert_eq!(p0.to_i32(), Some(123));
        
        let p1: f32 = -123.456;
        assert_eq!(p1.to_i32(), Some(-123));

        let p2: f32 = 0.0;
        assert_eq!(p2.to_i32(), Some(0));

        let p3: f32 = std::f32::MAX;
        assert_eq!(p3.to_i32(), None);

        let p4: f32 = std::f32::MIN;
        assert_eq!(p4.to_i32(), Some(i32::MIN));

        let p5: f32 = 16777216.0; // i32::MAX + 1 as f32
        assert_eq!(p5.to_i32(), None);

        let p6: f32 = -16777217.0; // i32::MIN - 1 as f32
        assert_eq!(p6.to_i32(), None);
    }
}#[cfg(test)]
mod tests_rug_198 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        assert_eq!(p0.to_i64(), Some(123));
        
        // Additional test cases
        let p1: f32 = -123.456;
        assert_eq!(p1.to_i64(), Some(-123));

        let p2: f32 = 0.0;
        assert_eq!(p2.to_i64(), Some(0));

        let p3: f32 = std::f32::MIN + 1.0;
        assert_eq!(p3.to_i64(), None);

        let p4: f32 = std::f32::MAX - 1.0;
        assert_eq!(p4.to_i64(), Some(std::i64::MAX));
    }
}#[cfg(test)]
mod tests_rug_199 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        p0.to_i128();
    }
}#[cfg(test)]
mod tests_rug_200 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;

        assert_eq!(<f32 as ToPrimitive>::to_usize(&p0), Some(42));
        
        // Additional test cases
        p0 = -1.0;
        assert_eq!(<f32 as ToPrimitive>::to_usize(&p0), None);

        p0 = 0.99;
        assert_eq!(<f32 as ToPrimitive>::to_usize(&p0), Some(0));

        p0 = std::u8::MAX as f32 + 1.0;
        assert_eq!(<f32 as ToPrimitive>::to_usize(&p0), None);

        p0 = std::u8::MAX as f32;
        assert_eq!(<f32 as ToPrimitive>::to_usize(&p0), Some(std::u8::MAX as usize));
    }
}#[cfg(test)]
mod tests_rug_201 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;

        assert_eq!(<f32 as ToPrimitive>::to_u8(&p0), Some(42u8));
        
        // Additional test cases
        let p1: f32 = -1.5;
        let p2: f32 = 0.99;
        let p3: f32 = 255.0;
        let p4: f32 = 256.0;
        let p5: f32 = f32::INFINITY;

        assert_eq!(<f32 as ToPrimitive>::to_u8(&p1), None);
        assert_eq!(<f32 as ToPrimitive>::to_u8(&p2), Some(0u8));
        assert_eq!(<f32 as ToPrimitive>::to_u8(&p3), Some(255u8));
        assert_eq!(<f32 as ToPrimitive>::to_u8(&p4), None);
        assert_eq!(<f32 as ToPrimitive>::to_u8(&p5), None);
    }
}#[cfg(test)]
mod tests_rug_202 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456; // Sample data for f32

        assert_eq!(<f32 as ToPrimitive>::to_u16(&p0), Some(123));
        assert_eq!(<f32 as ToPrimitive>::to_u16(&-1.0), None);
        assert_eq!(<f32 as ToPrimitive>::to_u16(&(u16::MAX as f32 + 1.0)), None);
        assert_eq!(<f32 as ToPrimitive>::to_u16(&(u16::MAX as f32)), Some(u16::MAX));
    }
}#[cfg(test)]
mod tests_rug_203 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.5;

        <f32 as ToPrimitive>::to_u32(&p0);
    }
}#[cfg(test)]
mod tests_rug_204 {
    use super::*;
    use crate::ToPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;

        <f32 as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_205 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456; // Sample data for f32

        p0.to_u128();
    }
}#[cfg(test)]
mod tests_rug_206 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        assert_eq!(<f32 as ToPrimitive>::to_f32(&p0), Some(123.456));
        
        // Additional test cases
        let p1: f32 = std::f32::NAN;
        assert_eq!(<f32 as ToPrimitive>::to_f32(&p1), Some(std::f32::NAN));

        let p2: f32 = std::f32::INFINITY;
        assert_eq!(<f32 as ToPrimitive>::to_f32(&p2), Some(std::f32::INFINITY));

        let p3: f32 = std::f32::NEG_INFINITY;
        assert_eq!(<f32 as ToPrimitive>::to_f32(&p3), Some(std::f32::NEG_INFINITY));
    }
}#[cfg(test)]
mod tests_rug_207 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as ToPrimitive>::to_f64(&p0);
    }
}#[cfg(test)]
mod tests_rug_208 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        assert_eq!(p0.to_isize(), Some(123));
        
        // Additional test cases
        let p1: f64 = -123.999;
        assert_eq!(p1.to_isize(), Some(-123));

        let p2: f64 = 0.0;
        assert_eq!(p2.to_isize(), Some(0));

        let p3: f64 = isize::MAX as f64 + 1.0;
        assert_eq!(p3.to_isize(), None);

        let p4: f64 = isize::MIN as f64 - 1.0;
        assert_eq!(p4.to_isize(), None);
    }
}#[cfg(test)]
mod tests_rug_209 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 127.0; // Sample data for f64

        p0.to_i8();
    }
}#[cfg(test)]
mod tests_rug_210 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        p0.to_i16();
    }
}#[cfg(test)]
mod tests_rug_211 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as ToPrimitive>::to_i32(&p0);
    }
}#[cfg(test)]
mod tests_rug_212 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as ToPrimitive>::to_i64(&p0);
    }
}#[cfg(test)]
mod tests_rug_213 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        assert_eq!(p0.to_i128(), Some(123));
        
        // Additional test cases
        let p1: f64 = -123.456;
        assert_eq!(p1.to_i128(), Some(-123));

        let p2: f64 = 0.0;
        assert_eq!(p2.to_i128(), Some(0));

        let p3: f64 = 18_446_744_073_709_551_615.0; // i128::MAX as f64
        assert_eq!(p3.to_i128(), Some(18_446_744_073_709_551_615));

        let p4: f64 = -18_446_744_073_709_551_615.0; // i128::MIN as f64
        assert_eq!(p4.to_i128(), Some(-18_446_744_073_709_551_615));

        let p5: f64 = 1.7976931348623157e+308; // f64::MAX
        assert_eq!(p5.to_i128(), None);

        let p6: f64 = -1.7976931348623157e+308; // f64::MIN
        assert_eq!(p6.to_i128(), None);
    }
}#[cfg(test)]
mod tests_rug_214 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.45;

        assert_eq!(<f64 as ToPrimitive>::to_usize(&p0), Some(123));
    }

    #[test]
    fn test_negative() {
        let p0: f64 = -123.45;

        assert_eq!(<f64 as ToPrimitive>::to_usize(&p0), None);
    }

    #[test]
    fn test_max_value() {
        let p0: f64 = usize::MAX as f64;

        assert_eq!(<f64 as ToPrimitive>::to_usize(&p0), Some(usize::MAX));
    }

    #[test]
    fn test_exceeding_max_value() {
        let p0: f64 = (usize::MAX as f64) + 1.0;

        assert_eq!(<f64 as ToPrimitive>::to_usize(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_215 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        assert_eq!(<f64 as ToPrimitive>::to_u8(&p0), Some(123));
    }

    #[test]
    fn test_negative_float() {
        let p0: f64 = -123.456;

        assert_eq!(<f64 as ToPrimitive>::to_u8(&p0), None);
    }

    #[test]
    fn test_zero() {
        let p0: f64 = 0.0;

        assert_eq!(<f64 as ToPrimitive>::to_u8(&p0), Some(0));
    }

    #[test]
    fn test_max_value() {
        let p0: f64 = u8::MAX as f64;

        assert_eq!(<f64 as ToPrimitive>::to_u8(&p0), Some(u8::MAX));
    }

    #[test]
    fn test_above_max_value() {
        let p0: f64 = (u8::MAX as f64) + 1.0;

        assert_eq!(<f64 as ToPrimitive>::to_u8(&p0), None);
    }

    #[test]
    fn test_below_zero() {
        let p0: f64 = -0.5;

        assert_eq!(<f64 as ToPrimitive>::to_u8(&p0), None);
    }
}#[cfg(test)]
mod tests_rug_216 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        <f64 as ToPrimitive>::to_u16(&p0);
    }
}#[cfg(test)]
mod tests_rug_217 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as ToPrimitive>::to_u32(&p0);
    }
}#[cfg(test)]
mod tests_rug_218 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_219 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        assert_eq!(p0.to_u128(), Some(123));
        
        // Additional test cases
        let p1: f64 = -1.0;
        let p2: f64 = 0.0;
        let p3: f64 = 18_446_744_073_709_551_615.0; // u64::MAX as f64
        let p4: f64 = 18_446_744_073_709_551_616.0; // u64::MAX as f64 + 1.0
        let p5: f64 = 340_282_346_638_528_859_811_704_183_484_516_925_440.0; // u128::MAX as f64
        let p6: f64 = 340_282_346_638_528_859_811_704_183_484_516_925_441.0; // u128::MAX as f64 + 1.0

        assert_eq!(p1.to_u128(), None);
        assert_eq!(p2.to_u128(), Some(0));
        assert_eq!(p3.to_u128(), Some(18_446_744_073_709_551_615)); // u64::MAX
        assert_eq!(p4.to_u128(), None);
        assert_eq!(p5.to_u128(), Some(340_282_346_638_528_859_811_704_183_484_516_925_440)); // u128::MAX
        assert_eq!(p6.to_u128(), None);
    }
}#[cfg(test)]
mod tests_rug_220 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as ToPrimitive>::to_f32(&p0);
    }
}#[cfg(test)]
mod tests_rug_221 {
    use super::*;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        assert_eq!(<f64 as ToPrimitive>::to_f64(&p0), Some(3.14));
    }
}#[cfg(test)]
mod tests_rug_222 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <i32 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_223 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 42;

        <isize as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_224 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 123;

        <isize as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_225 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        <isize as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_226 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 12345;

        <isize as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_227 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 123456789012345678901234567890123456789;

        assert_eq!(<isize>::from_i128(p0), if p0 <= isize::MAX as i128 && p0 >= isize::MIN as i128 { Some(p0 as isize) } else { None });
    }
}#[cfg(test)]
mod tests_rug_228 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <isize>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_229 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        <isize>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_230 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        <isize>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_231 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42; // Sample data for a u32

        <isize as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_232 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 12345;

        <isize as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_233 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42;

        <isize>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_234 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        <isize as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_235 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        <isize as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_236 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42; // Sample data for isize

        <i8 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_237 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <u32 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_238 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 42; // Sample data for i16

        <i8 as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_239 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 10;

        <i8 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_240 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 127; // Sample data within the range of i8

        <i8 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_241 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 127; // Sample data for i128

        assert_eq!(<i8 as FromPrimitive>::from_i128(p0), Some(127));
        assert_eq!(<i8 as FromPrimitive>::from_i128(p0 + 1), None);
    }
}#[cfg(test)]
mod tests_rug_242 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <i8>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_243 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 123;

        <i8 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_244 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 255; // Sample data for u16

        <i8>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_245 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42u32;

        assert_eq!(<i8 as FromPrimitive>::from_u32(p0), Some(42));
        assert_eq!(<i8 as FromPrimitive>::from_u32(u32::MAX), None);
    }
}#[cfg(test)]
mod tests_rug_246 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 123;

        assert_eq!(<i8 as FromPrimitive>::from_u64(p0), Some(123));
        assert_eq!(<i8 as FromPrimitive>::from_u64(256), None); // Out of range for i8
    }
}#[cfg(test)]
mod tests_rug_247 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42;

        assert_eq!(<i8 as FromPrimitive>::from_u128(p0), Some(42));
    }

    #[test]
    fn test_out_of_bounds() {
        let p0: u128 = 128; // This is out of bounds for i8

        assert_eq!(<i8 as FromPrimitive>::from_u128(p0), None);
    }
}#[cfg(test)]
mod tests_rug_248 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.45;

        let result: Option<i8> = <i8 as FromPrimitive>::from_f32(p0);
        assert_eq!(result, Some(123));
    }

    #[test]
    fn test_rug_out_of_range() {
        let p0: f32 = 300.0;

        let result: Option<i8> = <i8 as FromPrimitive>::from_f32(p0);
        assert_eq!(result, None);
    }

    #[test]
    fn test_rug_negative() {
        let p0: f32 = -123.45;

        let result: Option<i8> = <i8 as FromPrimitive>::from_f32(p0);
        assert_eq!(result, Some(-123));
    }

    #[test]
    fn test_rug_negative_out_of_range() {
        let p0: f32 = -300.0;

        let result: Option<i8> = <i8 as FromPrimitive>::from_f32(p0);
        assert_eq!(result, None);
    }
}#[cfg(test)]
mod tests_rug_249 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.45;

        <i8>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_250 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        assert_eq!(<i16 as FromPrimitive>::from_isize(p0), Some(12345));
        
        // Test edge cases
        p0 = i16::MAX as isize;
        assert_eq!(<i16 as FromPrimitive>::from_isize(p0), Some(i16::MAX));

        p0 = i16::MIN as isize;
        assert_eq!(<i16 as FromPrimitive>::from_isize(p0), Some(i16::MIN));

        p0 = (i16::MAX as isize) + 1;
        assert_eq!(<i16 as FromPrimitive>::from_isize(p0), None);

        p0 = (i16::MIN as isize) - 1;
        assert_eq!(<i16 as FromPrimitive>::from_isize(p0), None);
    }
}#[cfg(test)]
mod tests_rug_251 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i16 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_252 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 123;

        <i32 as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_253 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        let result = <i16 as FromPrimitive>::from_i32(p0);
        assert_eq!(result, Some(12345));
        
        // Test with a value that is out of range for i16
        p0 = 70000;
        let result_out_of_range = <i16 as FromPrimitive>::from_i32(p0);
        assert_eq!(result_out_of_range, None);
    }
}#[cfg(test)]
mod tests_rug_254 {
    use super::*;
    use crate::FromPrimitive;
    
    #[test]
    fn test_rug() {
        let mut p0: i64 = 123;

        <i16 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_255 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 32767; // Sample data within the range of i16

        assert_eq!(<i16 as FromPrimitive>::from_i128(p0), Some(32767));

        let p1: i128 = -32768; // Another sample data within the range of i16
        assert_eq!(<i16 as FromPrimitive>::from_i128(p1), Some(-32768));

        let p2: i128 = 32768; // Out of range for i16, should return None
        assert_eq!(<i16 as FromPrimitive>::from_i128(p2), None);

        let p3: i128 = -32769; // Out of range for i16, should return None
        assert_eq!(<i16 as FromPrimitive>::from_i128(p3), None);
    }
}#[cfg(test)]
mod tests_rug_256 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 12345;

        <i16 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_257 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; // Sample data for u8

        <i16 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_258 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42; // Sample data for u16

        <i16 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_259 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 100; // Sample data for a u32

        <i16 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_260 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        <i16 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_261 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 12345_u128; // Sample data for the first argument

        <i16 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_262 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <i16 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_263 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.45;

        <i16 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_264 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        let result: Option<i32> = <i32 as FromPrimitive>::from_isize(p0);
        assert_eq!(result, Some(12345));
    }
}#[cfg(test)]
mod tests_rug_265 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42_i8;

        <i32 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_266 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Sample data for i16

        <i32 as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_267 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_268 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i32 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_269 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 123456789012345678901234567890123456789;

        <i32 as FromPrimitive>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_270 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <i32 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_271 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        <i32 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_272 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 32769; // Sample data for u16

        <i32 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_273 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 12345;

        <i32 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_274 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        <i32 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_275 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;

        <i32 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_276 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        <i32 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_277 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <i32 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_278 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <i64 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_279 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 42;

        <i64 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_280 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        let result: Option<i64> = <i64 as FromPrimitive>::from_i16(p0);
        assert_eq!(result, Some(12345));
    }
}#[cfg(test)]
mod tests_rug_281 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42;

        let result: Option<i64> = <i64 as FromPrimitive>::from_i32(p0);
        assert_eq!(result, Some(42));
    }
}#[cfg(test)]
mod tests_rug_282 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 123456789;

        <i64 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_283 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 9223372036854775807i128; // Sample data within the range of i64

        <i64 as FromPrimitive>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_284 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <i64 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_285 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        let result: Option<i64> = <i64 as FromPrimitive>::from_u8(p0);
        assert_eq!(result, Some(42));
    }
}#[cfg(test)]
mod tests_rug_286 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42u16;

        <i64 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_287 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // Sample data for u32

        <i64 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_288 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 123456789;

        <i64 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_289 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 123456789012345678901234567890123456789;

        <i64>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_290 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <i64 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_291 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.45;

        <i64 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_292 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <i128 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_293 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 42;

        <i128 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_294 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 12345;

        <i128 as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_295 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42; // Sample data initialization

        <i128 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_296 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 9223372036854775807; // Sample data for i64

        <i128 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_297 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128

        <i128 as FromPrimitive>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_298 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <i128 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_299 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42u8;

        <i128 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_300 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42; // Sample data for u16 type

        <i128 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_301 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 4294967295; // Sample data for u32

        <i128 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_302 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890123456789;

        <i128 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_303 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 123456789012345678901234567890123456789;

        <i128 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_304 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        <i128 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_305 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        <i128 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_306 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <usize as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_307 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for i8

        <usize as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_308 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 123;

        <usize>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_309 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42; // Sample data for i32

        <usize>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_310 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <usize>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_311 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 42;

        <usize>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_312 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <usize as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_313 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        <usize as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_314 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42u16;

        <usize>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_315 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42;

        <usize>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_316 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        <usize>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_317 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        <usize>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_318 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 42.0;

        <usize>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_319 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 42.0;

        <usize as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_320 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123;

        <u8 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_321 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample initialization

        <u8 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_322 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42; // Sample data for i16

        assert_eq!(<u8 as FromPrimitive>::from_i16(p0), Some(42));
        
        // Testing edge cases
        p0 = -1;
        assert_eq!(<u8 as FromPrimitive>::from_i16(p0), None);

        p0 = 256;
        assert_eq!(<u8 as FromPrimitive>::from_i16(p0), None);
    }
}#[cfg(test)]
mod tests_rug_323 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42; // Sample data for i32

        <u8>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_324 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123;

        <u8>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_325 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 42;

        assert_eq!(<u8 as FromPrimitive>::from_i128(p0), Some(42));
        
        // Test with a value that is out of range for u8
        let p1: i128 = 256;
        assert_eq!(<u8 as FromPrimitive>::from_i128(p1), None);
    }
}#[cfg(test)]
mod tests_rug_326 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 255;

        <u8 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_327 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        <i32 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_328 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 255;

        <u8 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_329 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u8 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_330 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123; // Sample data for u64

        <u8 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_331 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        <u8 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_332 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        <u8 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_333 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <u8 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_334 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        <u16 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_335 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 123; // Sample data for i8

        let result: Option<u16> = <u16 as FromPrimitive>::from_i8(p0);
        assert_eq!(result, Some(123));
    }
}#[cfg(test)]
mod tests_rug_336 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 123;

        assert_eq!(<u16 as FromPrimitive>::from_i16(p0), Some(123));
        
        p0 = -1;
        assert_eq!(<u16 as FromPrimitive>::from_i16(p0), None);
    }
}#[cfg(test)]
mod tests_rug_337 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 100;

        <u16 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_338 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 123;

        <u16 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_339 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 300i128; // Sample data for i128

        <u16 as FromPrimitive>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_340 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <u16 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_341 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 10u8;

        <u16 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_342 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42u16;

        <u16 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_343 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 10_000u32;

        <u16 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_344 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 12345;

        <u16 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_345 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;

        <u16 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_346 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456; // Sample data for f32

        <u16 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_347 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.0;

        <u16 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_348 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 42;

        <u32 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_349 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 42;

        <u32 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_350 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        <u32 as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_351 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 123; // Sample data for i32

        let result: Option<u32> = <u32 as FromPrimitive>::from_i32(p0);
        assert_eq!(result, Some(123));
    }
}#[cfg(test)]
mod tests_rug_352 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 12345;

        <u32 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_353 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;

        assert_eq!(<u32 as FromPrimitive>::from_i128(p0), Some(42));
        
        // Test edge case where the value is out of range for u32
        p0 = -1;
        assert_eq!(<u32 as FromPrimitive>::from_i128(p0), None);

        // Test upper bound of i128 that fits into u32
        p0 = 4_294_967_295; // u32::MAX
        assert_eq!(<u32 as FromPrimitive>::from_i128(p0), Some(4_294_967_295));

        // Test value greater than u32::MAX
        p0 = 4_294_967_296;
        assert_eq!(<u32 as FromPrimitive>::from_i128(p0), None);
    }
}#[cfg(test)]
mod tests_rug_354 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <u32 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_355 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        assert_eq!(<u32 as FromPrimitive>::from_u8(p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_356 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42u16;

        <u32 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_357 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_358 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        <u32 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_359 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;
        
        <u32 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_360 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <u32 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_361 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.45;

        <u32 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_362 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <u64 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_363 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 123;

        let result: Option<u64> = <u64 as FromPrimitive>::from_i8(p0);
        assert_eq!(result, Some(123));
    }
}#[cfg(test)]
mod tests_rug_364 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Example value for i16

        <u64 as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_365 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42;

        <u64 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_366 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <u64 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_367 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42_i128;

        assert_eq!(<u64>::from_i128(p0), Some(42));
        
        // Test edge cases
        let max_u64_as_i128: i128 = u64::MAX as i128;
        let min_u64_as_i128: i128 = 0_i128;
        let out_of_range_positive: i128 = (u64::MAX as i128) + 1;
        let out_of_range_negative: i128 = -1_i128;

        assert_eq!(<u64>::from_i128(max_u64_as_i128), Some(u64::MAX));
        assert_eq!(<u64>::from_i128(min_u64_as_i128), Some(0));
        assert_eq!(<u64>::from_i128(out_of_range_positive), None);
        assert_eq!(<u64>::from_i128(out_of_range_negative), None);
    }
}#[cfg(test)]
mod tests_rug_368 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42_usize;

        <u64 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_369 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42; // Sample data for u8

        <u64 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_370 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42; // Sample data for u16

        <u64 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_371 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u64 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_372 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890;

        assert_eq!(<u64 as FromPrimitive>::from_u64(p0), Some(1234567890));
    }
}#[cfg(test)]
mod tests_rug_373 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;

        <u64 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_374 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 42.0;

        <u64 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_375 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        <u64 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_376 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789012345;

        let result = <u128 as FromPrimitive>::from_isize(p0);
        assert_eq!(result, Some(123456789012345));
    }
}#[cfg(test)]
mod tests_rug_377 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for initialization

        let result = <u128 as FromPrimitive>::from_i8(p0);
        assert_eq!(result, Some(42u128));
    }
}#[cfg(test)]
mod tests_rug_378 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Sample data for i16

        let result = <u128 as FromPrimitive>::from_i16(p0);
        assert_eq!(result, Some(32767));
    }
}#[cfg(test)]
mod tests_rug_379 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <u128 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_380 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 1234567890;

        assert_eq!(<u128 as FromPrimitive>::from_i64(p0), Some(1234567890));
        
        // Test edge cases
        p0 = -1;
        assert_eq!(<u128 as FromPrimitive>::from_i64(p0), None);

        p0 = i64::MAX;
        assert_eq!(<u128 as FromPrimitive>::from_i64(p0), Some(i64::MAX as u128));

        p0 = i64::MIN;
        assert_eq!(<u128 as FromPrimitive>::from_i64(p0), None);
    }
}#[cfg(test)]
mod tests_rug_381 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789_i128;

        <u128 as FromPrimitive>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_382 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <u128 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_383 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u128 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_384 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42;

        assert_eq!(<u128 as FromPrimitive>::from_u16(p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_385 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u128 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_386 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890123456789;

        assert_eq!(<u128 as FromPrimitive>::from_u64(p0), Some(1234567890123456789));
    }
}#[cfg(test)]
mod tests_rug_387 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 123456789012345678901234567890123456789;

        <u128 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_388 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456; // Sample data for f32

        <u128 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_389 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <u128 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_390 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456;

        <f32 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_391 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for i8

        <f32 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_392 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        let result: Option<f32> = <f32 as FromPrimitive>::from_i16(p0);
        assert_eq!(result, Some(12345.0));
    }
}#[cfg(test)]
mod tests_rug_393 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <f32 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_394 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <f32 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_395 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 12345678901234567890123456789012345678;

        <f32 as FromPrimitive>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_396 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <f32 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_397 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42; // Sample data for u8

        <f32 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_398 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 12345;

        <f32 as FromPrimitive>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_399 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <f32 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_400 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890;

        <f32 as FromPrimitive>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_401 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 123456789012345678901234567890123456789;

        <f32 as FromPrimitive>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_402 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <i32 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_403 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f32 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_404 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <f64 as FromPrimitive>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_405 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <f64 as FromPrimitive>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_406 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: i16 = 32767;

        <f64 as FromPrimitive>::from_i16(p0);
    }
}#[cfg(test)]
mod tests_rug_407 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        <f64 as FromPrimitive>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_408 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        <f64 as FromPrimitive>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_409 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9_223_372_036_854_775_807_i128; // Sample data for i128

        <f64 as FromPrimitive>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_410 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <f64 as FromPrimitive>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_411 {
    use super::*;
    use crate::cast::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; // Sample data for u8

        <f64 as FromPrimitive>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_412 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        assert_eq!(<f64 as FromPrimitive>::from_u16(p0), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_413 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; // Sample data for u32

        <f64 as FromPrimitive>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_414 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;

        assert_eq!(<f64 as FromPrimitive>::from_u64(p0), Some(123456789.0));
    }
}#[cfg(test)]
mod tests_rug_415 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;

        assert_eq!(<f64>::from_u128(p0), Some(1.2345678901234568e+38));
    }
}#[cfg(test)]
mod tests_rug_416 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        <f64 as FromPrimitive>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_417 {
    use super::*;
    use crate::FromPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14159;

        <i32 as FromPrimitive>::from_f64(p0);
        <u32 as FromPrimitive>::from_f64(p0);
        <f32 as FromPrimitive>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_418 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping(42);

        <core::num::Wrapping<u32> as ToPrimitive>::to_isize(&p0);
    }
}#[cfg(test)]
mod tests_rug_419 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping::<u32>(42);

        <core::num::Wrapping<u32>>::to_i8(&p0);
    }
}#[cfg(test)]
mod tests_rug_420 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping::<u32>(42);

        <core::num::Wrapping<u32> as ToPrimitive>::to_i16(&p0);
    }
}#[cfg(test)]
mod tests_rug_421 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping::<u32>(42);

        assert_eq!(<Wrapping<u32> as ToPrimitive>::to_i32(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_422 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping(42);

        <core::num::Wrapping<u32> as ToPrimitive>::to_i64(&p0);
    }
}#[cfg(test)]
mod tests_rug_423 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0 = Wrapping::<u32>(42); // create the local variable p0 with type core::num::Wrapping<T>

        assert_eq!(<core::num::Wrapping<u32> as ToPrimitive>::to_i128(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_424 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping::<u32>(42);

        assert_eq!(<Wrapping<u32> as ToPrimitive>::to_usize(&p0), Some(42));
    }
}#[cfg(test)]
mod tests_rug_425 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping(42);

        assert_eq!(p0.to_u8(), Some(42));
    }
}#[cfg(test)]
mod tests_rug_426 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping(42);

        <Wrapping<u32> as ToPrimitive>::to_u16(&p0);
    }
}#[cfg(test)]
mod tests_rug_427 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping::<u32>(42);

        assert_eq!(p0.to_u32(), Some(42));
    }
}#[cfg(test)]
mod tests_rug_428 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping::<u32>(42);

        <core::num::Wrapping<u32> as ToPrimitive>::to_u64(&p0);
    }
}#[cfg(test)]
mod tests_rug_429 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: Wrapping<u32> = Wrapping::<u32>(42);

        <core::num::Wrapping<u32> as ToPrimitive>::to_u128(&p0);
    }
}#[cfg(test)]
mod tests_rug_430 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping::<u32>(42);

        assert_eq!(p0.to_f32(), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_431 {
    use super::*;
    use crate::ToPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: Wrapping<u32> = Wrapping(42);

        assert_eq!(p0.to_f64(), Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_432 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42; // Sample data for isize

        <core::num::Wrapping<isize>>::from_isize(p0);
    }
}#[cfg(test)]
mod tests_rug_433 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <core::num::Wrapping<i32>>::from_i8(p0);
    }
}#[cfg(test)]
mod tests_rug_434 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: i16 = 42; // Sample data to initialize the variable

        <core::num::Wrapping<i32>>::from_i16(p0); // Filling in generic args
    }
}#[cfg(test)]
mod tests_rug_435 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: i32 = 42;

        <core::num::Wrapping<i32>>::from_i32(p0);
    }
}#[cfg(test)]
mod tests_rug_436 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: i64 = 12345;

        <core::num::Wrapping<i32>>::from_i64(p0);
    }
}#[cfg(test)]
mod tests_rug_437 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: i128 = 123456789012345678901234567890123456789;

        <core::num::Wrapping<i128>>::from_i128(p0);
    }
}#[cfg(test)]
mod tests_rug_438 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <core::num::Wrapping<u32>>::from_usize(p0);
    }
}#[cfg(test)]
mod tests_rug_439 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: u8 = 42u8;

        <core::num::Wrapping<u32>>::from_u8(p0);
    }
}#[cfg(test)]
mod tests_rug_440 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: u16 = 42u16;

        <core::num::Wrapping<u16>>::from_u16(p0);
    }
}#[cfg(test)]
mod tests_rug_441 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; // Sample data for u32

        <core::num::Wrapping<u32>>::from_u32(p0);
    }
}#[cfg(test)]
mod tests_rug_442 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: u64 = 1234567890;

        <core::num::Wrapping<u64>>::from_u64(p0);
    }
}#[cfg(test)]
mod tests_rug_443 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;

        <core::num::Wrapping<u128>>::from_u128(p0);
    }
}#[cfg(test)]
mod tests_rug_444 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: f32 = 42.5;

        <core::num::Wrapping<u8>>::from_f32(p0);
    }
}#[cfg(test)]
mod tests_rug_445 {
    use super::*;
    use crate::FromPrimitive;
    use core::num::Wrapping;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        <core::num::Wrapping<i32>>::from_f64(p0);
    }
}#[cfg(test)]
mod tests_rug_446 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 127; // Example value that can be represented by u8

        assert_eq!(<u8 as NumCast>::from(p0), Some(127));

        let p1: i32 = -1; // Example value that cannot be represented by u8
        assert_eq!(<u8 as NumCast>::from(p1), None);

        let p2: f64 = 255.99; // Example float value that will be truncated to u8 max value
        assert_eq!(<u8 as NumCast>::from(p2), Some(255));

        let p3: f64 = -0.1; // Example negative float value that cannot be represented by u8
        assert_eq!(<u8 as NumCast>::from(p3), None);

        let p4: i64 = 256; // Example value that is out of range for u8
        assert_eq!(<u8 as NumCast>::from(p4), None);
    }
}#[cfg(test)]
mod tests_rug_447 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 123; // Example value for N that satisfies ToPrimitive and Sized

        assert_eq!(<u16 as NumCast>::from(p0), Some(123));
        
        let p1: i32 = -1; // Example negative value
        assert_eq!(<u16 as NumCast>::from(p1), None);

        let p2: u32 = 65535; // Max value for u16
        assert_eq!(<u16 as NumCast>::from(p2), Some(65535));

        let p3: u32 = 65536; // Value out of range for u16
        assert_eq!(<u16 as NumCast>::from(p3), None);

        let p4: f32 = 123.0;
        assert_eq!(<u16 as NumCast>::from(p4), Some(123));

        let p5: f32 = 65535.9; // Value that will be truncated
        assert_eq!(<u16 as NumCast>::from(p5), Some(65535));

        let p6: f32 = 65536.0; // Value out of range for u16
        assert_eq!(<u16 as NumCast>::from(p6), None);
    }
}#[cfg(test)]
mod tests_rug_448 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 123;

        assert_eq!(<u32 as NumCast>::from(p0), Some(123));
    }
}#[cfg(test)]
mod tests_rug_449 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42; // Example concrete implementation of ToPrimitive

        assert_eq!(<u64 as NumCast>::from(p0), Some(42));
    }

    #[test]
    fn test_rug_large_value() {
        let mut p0: i64 = u64::MAX as i64 + 1; // Value larger than u64 can represent

        assert_eq!(<u64 as NumCast>::from(p0), None);
    }

    #[test]
    fn test_rug_negative_value() {
        let mut p0: i32 = -1; // Negative value which cannot be represented by u64

        assert_eq!(<u64 as NumCast>::from(p0), None);
    }

    #[test]
    fn test_rug_floating_point() {
        let mut p0: f64 = 123.456; // Floating point value

        assert_eq!(<u64 as NumCast>::from(p0), Some(123));
    }
}#[cfg(test)]
mod tests_rug_450 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 42;

        assert_eq!(<u128 as NumCast>::from(p0), Some(42));
        
        let p1: u128 = 100;
        assert_eq!(<u128 as NumCast>::from(p1), Some(100));

        let p2: i64 = -5;
        assert_eq!(<u128 as NumCast>::from(p2), None);

        let p3: f64 = 123.456;
        assert_eq!(<u128 as NumCast>::from(p3), Some(123));

        let p4: usize = 999;
        assert_eq!(<u128 as NumCast>::from(p4), Some(999));
    }
}#[cfg(test)]
mod tests_rug_451 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 123; // Using a sample concrete type that satisfies `ToPrimitive`

        <usize as NumCast>::from(p0);

        let p1: u64 = 456;
        <usize as NumCast>::from(p1);

        let p2: f32 = 789.0;
        <usize as NumCast>::from(p2);

        let p3: i64 = -1; // Out of range for usize
        assert_eq!(<usize as NumCast>::from(p3), None);

        let p4: u128 = 18_446_744_073_709_551_615_u128; // Max value of u64
        <usize as NumCast>::from(p4);
    }
}#[cfg(test)]
mod tests_rug_452 {
    use super::*;
    use crate::NumCast;
    use crate::cast::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123; // Example value satisfying the ToPrimitive bound

        let result: Option<i8> = <i8 as NumCast>::from(p0);
        assert_eq!(result, Some(123));

        let p0_out_of_range: i64 = 128; // Out of range for i8
        let result_out_of_range: Option<i8> = <i8 as NumCast>::from(p0_out_of_range);
        assert_eq!(result_out_of_range, None);

        let p0_negative: i64 = -129; // Out of range for i8
        let result_negative: Option<i8> = <i8 as NumCast>::from(p0_negative);
        assert_eq!(result_negative, None);
    }
}#[cfg(test)]
mod tests_rug_453 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345; // Example value that satisfies ToPrimitive and Sized

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, Some(12345));
    }

    #[test]
    fn test_rug_out_of_range() {
        let mut p0: i32 = 100000; // Example value that is out of range for i16

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, None);
    }

    #[test]
    fn test_rug_negative() {
        let mut p0: i32 = -12345; // Example negative value that satisfies ToPrimitive and Sized

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, Some(-12345));
    }

    #[test]
    fn test_rug_negative_out_of_range() {
        let mut p0: i32 = -100000; // Example negative value that is out of range for i16

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, None);
    }

    #[test]
    fn test_rug_from_f32() {
        let mut p0: f32 = 12345.0; // Example value that satisfies ToPrimitive and Sized

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, Some(12345));
    }

    #[test]
    fn test_rug_from_f32_out_of_range() {
        let mut p0: f32 = 100000.0; // Example value that is out of range for i16

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, None);
    }

    #[test]
    fn test_rug_from_f32_negative() {
        let mut p0: f32 = -12345.0; // Example negative value that satisfies ToPrimitive and Sized

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, Some(-12345));
    }

    #[test]
    fn test_rug_from_f32_negative_out_of_range() {
        let mut p0: f32 = -100000.0; // Example negative value that is out of range for i16

        let result: Option<i16> = <i16 as NumCast>::from(p0);

        assert_eq!(result, None);
    }
}#[cfg(test)]
mod tests_rug_454 {
    use super::*;
    use crate::cast::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i64 = 123; // Example value that satisfies the ToPrimitive trait bounds

        let result: Option<i32> = <i32 as NumCast>::from(p0);
        
        assert_eq!(result, Some(123));
    }
}#[cfg(test)]
mod tests_rug_455 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 123; // Concrete implementation of N that satisfies the bounds

        let result: Option<i64> = <i64 as NumCast>::from(p0);

        assert_eq!(result, Some(123));
    }
}#[cfg(test)]
mod tests_rug_456 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 12345; // Concrete implementation of N that satisfies ToPrimitive and core::marker::Sized

        let result: Option<i128> = <i128 as NumCast>::from(p0);

        assert_eq!(result, Some(12345));
    }
}#[cfg(test)]
mod tests_rug_457 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 123; // Concrete implementation of `N` that satisfies bounds

        let result = <isize as NumCast>::from(p0);
        assert_eq!(result, Some(123));
    }
}#[cfg(test)]
mod tests_rug_458 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42; // Example concrete implementation of N that satisfies ToPrimitive and core::marker::Sized

        let result = <f32 as NumCast>::from(p0);
        assert_eq!(result, Some(42.0));
    }
}#[cfg(test)]
mod tests_rug_459 {
    use super::*;
    use crate::NumCast;
    use crate::ToPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 123; // Example value of a type that implements ToPrimitive

        let result = <f64 as NumCast>::from(p0);
        assert_eq!(result, Some(123.0));
    }
}#[cfg(test)]
mod tests_rug_461 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 65; // Sample data for u8

        <u8 as AsPrimitive<char>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_462 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; // Sample data for u8

        <u8 as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_463 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        let result: f64 = <u8 as AsPrimitive<f64>>::as_(p0);
        assert_eq!(result, 42.0);
    }
}#[cfg(test)]
mod tests_rug_464 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u8 as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_465 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u8 as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_466 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42; 

        <u8 as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_467 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u8 as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_468 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u8 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_469 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        <u8 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_470 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 123;

        <u8 as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_471 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 123;

        <u8 as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_472 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        <u8 as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_473 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        let result: i64 = <u8 as AsPrimitive<i64>>::as_(p0);
        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_474 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42u8;

        <u8 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_475 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 42;

        let result: i128 = <u8 as AsPrimitive<i128>>::as_(p0);
        assert_eq!(result, 42_i128);
    }
}#[cfg(test)]
mod tests_rug_476 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        let result: f32 = <i8 as AsPrimitive<f32>>::as_(p0);
        assert_eq!(result, 42.0);
    }
}#[cfg(test)]
mod tests_rug_477 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i8 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_478 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: i8 = 127; // Sample data for i8

        let result: u8 = <i8 as AsPrimitive<u8>>::as_(p0);
        assert_eq!(result, 127);
    }
}#[cfg(test)]
mod tests_rug_479 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 123_i8;

        let result: u16 = <i8 as AsPrimitive<u16>>::as_(p0);

        assert_eq!(result, 123_u16);
    }
}#[cfg(test)]
mod tests_rug_480 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for i8

        let result: u32 = <i8 as AsPrimitive<u32>>::as_(p0);

        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_481 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for i8

        let result: u64 = <i8 as AsPrimitive<u64>>::as_(p0);

        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_482 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42; // Sample data for i8

        <i8 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_483 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42_i8;

        <i8 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_484 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i8 as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_485 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 123_i8;

        let result: i16 = <i8 as AsPrimitive<i16>>::as_(p0);
        assert_eq!(result, 123_i16);
    }
}#[cfg(test)]
mod tests_rug_486 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        let result: i32 = <i8 as AsPrimitive<i32>>::as_(p0);
        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_487 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i8 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_488 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42;

        <i8 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_489 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i8 = 42_i8; // Sample data for i8

        <i8 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_490 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42u16;

        <u16 as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_491 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        <u16 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_492 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 257; // Sample data for u16

        let result: u8 = <u16 as AsPrimitive<u8>>::as_(p0);
        assert_eq!(result, 1); // Since 257 % 256 = 1
    }
}#[cfg(test)]
mod tests_rug_493 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        <u16 as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_494 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        <u16 as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_495 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42u16;

        <u16 as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_496 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42;

        <u16 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_497 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 500;

        <u16 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_498 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 255; // Sample data for u16

        let result: i8 = <u16 as AsPrimitive<i8>>::as_(p0);

        // You might want to assert the result if needed
        assert_eq!(result, -1); // Since 255 as i8 is -1 due to overflow
    }
}#[cfg(test)]
mod tests_rug_499 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 32768;

        let result: i16 = <u16 as AsPrimitive<i16>>::as_(p0);
        assert_eq!(result, -32768); // Example assertion based on the conversion
    }
}#[cfg(test)]
mod tests_rug_500 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 500u16;

        <u16 as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_501 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42;

        <u16 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_502 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u16 = 42;

        <u16 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_503 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42; // Sample data for u16

        <u16 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_504 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        let result: f32 = <i16 as AsPrimitive<f32>>::as_(p0);
        assert_eq!(result, 42.0);
    }
}#[cfg(test)]
mod tests_rug_505 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        <i16 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_506 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 123;

        <i16 as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_507 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        <i16 as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_508 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        let result: u32 = <i16 as AsPrimitive<u32>>::as_(p0);

        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_509 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        let result: u64 = <i16 as AsPrimitive<u64>>::as_(p0);

        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_510 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        <i16 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_511 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42; // Sample data for i16

        let result: u128 = <i16 as AsPrimitive<u128>>::as_(p0);
        assert_eq!(result, 42u128);
    }
}#[cfg(test)]
mod tests_rug_512 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 123; // Sample data for i16

        <i16 as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_513 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        <i16 as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_514 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Sample data for i16

        <i16 as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_515 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 12345;

        <i16 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_516 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 42;

        <i16 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_517 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i16 = 32767; // Sample data for i16

        <i16 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_518 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        let result: f32 = <u32 as AsPrimitive<f32>>::as_(p0);

        assert_eq!(result, 42.0);
    }
}#[cfg(test)]
mod tests_rug_519 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_520 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; // Sample data for u32

        <u32 as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_521 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 65535;

        <u32 as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_522 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; // Sample data for u32

        <u32 as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_523 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        let result: u64 = <u32 as AsPrimitive<u64>>::as_(p0);
        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_524 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u32 = 42;

        <u32 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_525 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_526 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 127; // Sample data for u32

        let result: i8 = <u32 as AsPrimitive<i8>>::as_(p0);

        assert_eq!(result, 127);
    }
}#[cfg(test)]
mod tests_rug_527 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 12345u32;

        let result: i16 = <u32 as AsPrimitive<i16>>::as_(p0);

        // You can add assertions to check the result if needed
        assert_eq!(result, 12345i16);
    }
}#[cfg(test)]
mod tests_rug_528 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42; // Sample data for u32

        let result: i32 = <u32 as AsPrimitive<i32>>::as_(p0);
        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_529 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        <u32 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_530 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 12345u32;

        <u32 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_531 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42u32;

        <u32 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_532 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_533 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_534 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 128;

        <i32 as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_535 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        <i32 as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_536 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        let result: u32 = <i32 as AsPrimitive<u32>>::as_(p0);

        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_537 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_538 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_539 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_540 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 127;

        <i32 as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_541 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 1000;

        let result: i16 = <i32 as AsPrimitive<i16>>::as_(p0);
        assert_eq!(result, 1000);
    }
}#[cfg(test)]
mod tests_rug_542 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_543 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 42;

        <i32 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_544 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: i32 = 42;

        <i32 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_545 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i32 = 12345;

        <i32 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_546 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;

        <u64 as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_547 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;

        <u64 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_548 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890;

        let result: u8 = <u64 as AsPrimitive<u8>>::as_(p0);

        // You might want to assert the result for correctness
        assert_eq!(result, (1234567890 % 256) as u8);
    }
}#[cfg(test)]
mod tests_rug_549 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        let result: u16 = p0.as_();
        assert_eq!(result, 12345);
    }
}#[cfg(test)]
mod tests_rug_550 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890;

        <u64 as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_551 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 1234567890; // Sample data for u64

        <u64 as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_552 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u64 = 12345;

        <u64 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_553 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 18446744073709551615u64; // Maximum value for u64

        let result: u128 = <u64 as AsPrimitive<u128>>::as_(p0);

        assert_eq!(result, 18446744073709551615u128);
    }
}#[cfg(test)]
mod tests_rug_554 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123;

        let result: i8 = <u64 as AsPrimitive<i8>>::as_(p0);
        assert_eq!(result, 123_i8);
    }
}#[cfg(test)]
mod tests_rug_555 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 12345;

        let result: i16 = <u64 as AsPrimitive<i16>>::as_(p0);
        assert_eq!(result, 12345); // This assertion might fail if the value exceeds i16::MAX
    }
}#[cfg(test)]
mod tests_rug_556 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789;

        let result: i32 = <u64 as AsPrimitive<i32>>::as_(p0);

        // You can add assertions here if needed
        assert_eq!(result, 123456789_i32);
    }
}#[cfg(test)]
mod tests_rug_557 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890;

        <u64 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_558 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890;

        <u64 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_559 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 123456789012345;

        let result: i128 = <u64 as AsPrimitive<i128>>::as_(p0);

        assert_eq!(result, 123456789012345);
    }
}#[cfg(test)]
mod tests_rug_560 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        let result: f32 = <i64 as AsPrimitive<f32>>::as_(p0);

        assert_eq!(result, 123456789.0);
    }
}#[cfg(test)]
mod tests_rug_561 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        let result: f64 = <i64 as AsPrimitive<f64>>::as_(p0);
        assert_eq!(result, 123456789.0);
    }
}#[cfg(test)]
mod tests_rug_562 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123; // Sample data for i64

        <i64 as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_563 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        let result: u16 = <i64 as AsPrimitive<u16>>::as_(p0);

        assert_eq!(result, 12345);
    }
}#[cfg(test)]
mod tests_rug_564 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        let result: u32 = <i64 as AsPrimitive<u32>>::as_(p0);
        assert_eq!(result, 123456789);
    }
}#[cfg(test)]
mod tests_rug_565 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_566 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_567 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_568 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_569 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_570 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345_i64;

        <i64 as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_571 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 12345;

        <i64 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_572 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        <i64 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_573 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i64 = 123456789;

        let result: i128 = <i64 as AsPrimitive<i128>>::as_(p0);
        assert_eq!(result, 123456789);
    }
}#[cfg(test)]
mod tests_rug_574 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 18446744073709551615; // Sample data for u128

        <u128 as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_576 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42;

        <u128 as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_577 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42;

        let result: u16 = <u128 as AsPrimitive<u16>>::as_(p0);
        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_578 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        <u128 as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_579 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42;

        <u128 as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_580 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        <u128 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_582 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 12345678901234567890123456789012345678;

        let result: i8 = <u128 as AsPrimitive<i8>>::as_(p0);

        // You might want to assert something about the result, but for now, this is a valid call.
    }
}#[cfg(test)]
mod tests_rug_583 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 42u128;

        <u128 as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_584 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        let result: i32 = <u128 as AsPrimitive<i32>>::as_(p0);
        assert_eq!(result, 42i32); // This assertion will pass if the value fits within the range of i32
    }
}#[cfg(test)]
mod tests_rug_585 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: u128 = 4294967295u128; // Sample data for u128

        let result: i64 = <u128 as AsPrimitive<i64>>::as_(p0);
        assert_eq!(result, 4294967295i64);
    }
}#[cfg(test)]
mod tests_rug_586 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 42u128;

        <u128 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_587 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: u128 = 340282366920938463463374607431768211455; // Example value for u128

        <u128 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_588 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9_223_372_036_854_775_807_i128; // Sample data for i128

        let result: f32 = <i128 as AsPrimitive<f32>>::as_(p0);

        assert_eq!(result, 9_223_372_036_854_775_807.0);
    }
}#[cfg(test)]
mod tests_rug_589 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9_223_372_036_854_775_807; // Sample data for i128

        <i128 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_590 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;

        let result: u8 = <i128 as AsPrimitive<u8>>::as_(p0);

        // You can add assertions to verify the result if needed
        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_591 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 12345_i128; // Sample data for i128

        let result: u16 = <i128 as AsPrimitive<u16>>::as_(p0);
        assert_eq!(result, 12345_u16); // Ensure the cast is correct
    }
}#[cfg(test)]
mod tests_rug_592 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42_i128;

        let result: u32 = <i128 as AsPrimitive<u32>>::as_(p0);
        
        // Optional: Add assertions to verify the result
        assert_eq!(result, 42_u32);
    }
}#[cfg(test)]
mod tests_rug_593 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807i128; // Sample data for i128

        let result: u64 = <i128 as AsPrimitive<u64>>::as_(p0);

        assert_eq!(result, 9223372036854775807u64);
    }
}#[cfg(test)]
mod tests_rug_594 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42;

        let result: usize = <i128 as AsPrimitive<usize>>::as_(p0);
        assert_eq!(result, 42);
    }
}#[cfg(test)]
mod tests_rug_595 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: i128 = 9223372036854775807i128; // Sample data for i128

        <i128 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_596 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789;

        let result: i8 = <i128 as AsPrimitive<i8>>::as_(p0);
        // You might want to assert the result if needed
    }
}#[cfg(test)]
mod tests_rug_597 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 123456789012345678901234567890123456789;

        let result: i16 = <i128 as AsPrimitive<i16>>::as_(p0);
        // You might want to assert the result if needed
    }
}#[cfg(test)]
mod tests_rug_598 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 42_i128;

        let result: i32 = <i128 as AsPrimitive<i32>>::as_(p0);

        // Optional: Add an assertion to verify the result if needed
        assert_eq!(result, 42_i32);
    }
}#[cfg(test)]
mod tests_rug_599 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9_223_372_036_854_775_807; // This is the max value for i64

        let result: i64 = <i128 as AsPrimitive<i64>>::as_(p0);

        assert_eq!(result, 9_223_372_036_854_775_807);
    }
}#[cfg(test)]
mod tests_rug_600 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807_i128; // Example sample data for i128

        let result: isize = <i128 as AsPrimitive<isize>>::as_(p0);

        // You can add assertions here to verify the result if needed
    }
}#[cfg(test)]
mod tests_rug_601 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: i128 = 9223372036854775807; // Sample data for i128

        <i128 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_602 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <usize as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_603 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <usize as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_604 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 256; // Sample data for usize

        let result: u8 = <usize as AsPrimitive<u8>>::as_(p0);
        
        assert_eq!(result, 0); // Since 256 cannot fit into u8, it will wrap around to 0
    }
}#[cfg(test)]
mod tests_rug_605 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <usize as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_606 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <usize as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_607 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <usize as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_608 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <usize as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_609 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 123456789;

        <usize as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_610 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 123;

        <usize as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_611 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <usize as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_612 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <usize as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_613 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 12345;

        <usize as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_614 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: usize = 123456;

        <usize as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_615 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: usize = 42;

        <usize as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_616 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <isize as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_617 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <isize as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_618 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 12345;

        <isize as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_619 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        let result: u16 = <isize as AsPrimitive<u16>>::as_(p0);

        assert_eq!(result, 12345);
    }
}#[cfg(test)]
mod tests_rug_620 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        let result: u32 = <isize as AsPrimitive<u32>>::as_(p0);
        assert_eq!(result, 12345);
    }
}#[cfg(test)]
mod tests_rug_621 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789;

        <isize as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_622 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <isize as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_623 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 123456789;

        <isize as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_624 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        <isize as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_625 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 12345;

        let result: i16 = <isize as AsPrimitive<i16>>::as_(p0);

        // Optional: Add an assertion to check the result
        assert_eq!(result, 12345);
    }
}#[cfg(test)]
mod tests_rug_626 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <isize as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_627 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: isize = 42;

        <isize as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_628 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42;

        <isize as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_629 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: isize = 42; // Sample data for isize

        <isize as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_630 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<f32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_631 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 1.234;

        <f32 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_632 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 128.5;

        let result: u8 = <f32 as AsPrimitive<u8>>::as_(p0);
        assert_eq!(result, 128); // Example assertion based on the cast
    }
}#[cfg(test)]
mod tests_rug_633 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_634 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        let result: u32 = <f32 as AsPrimitive<u32>>::as_(p0);
        
        // Example assertion, you might want to change this based on your specific needs
        assert_eq!(result, 123);
    }
}#[cfg(test)]
mod tests_rug_635 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        let result: u64 = <f32 as AsPrimitive<u64>>::as_(p0);

        // You might want to add an assertion here to check the result
        assert_eq!(result, 123);
    }
}#[cfg(test)]
mod tests_rug_636 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_637 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: f32 = 123.456;

        let result: u128 = <f32 as AsPrimitive<u128>>::as_(p0);
        
        // You can add assertions here if needed
        assert_eq!(result, 123u128); // Note: This assertion may not be accurate due to the loss of fractional part
    }
}#[cfg(test)]
mod tests_rug_638 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 128.5;

        <f32 as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_639 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_640 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_641 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_642 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_643 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f32 = 123.456;

        <f32 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_644 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: f64 = 123.456;

        let result: f32 = <f64 as AsPrimitive<f32>>::as_(p0);
        assert_eq!(result, 123.456f32);
    }
}#[cfg(test)]
mod tests_rug_645 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14159;

        <f64 as AsPrimitive<f64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_646 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.45;

        let result: u8 = <f64 as AsPrimitive<u8>>::as_(p0);
        assert_eq!(result, 123); // Example assertion based on the conversion logic
    }
}#[cfg(test)]
mod tests_rug_647 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_648 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        let result: u32 = <f64 as AsPrimitive<u32>>::as_(p0);

        assert_eq!(result, 123);
    }
}#[cfg(test)]
mod tests_rug_649 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_650 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_651 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_652 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.45;

        <f64 as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_653 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;
        
        <f64 as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_654 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 3.14;

        <f64 as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_655 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_656 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_657 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: f64 = 123.456;

        <f64 as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_658 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <char as AsPrimitive<char>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_659 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'A';

        let result: u8 = <char as AsPrimitive<u8>>::as_(p0);

        // Optionally, you can add an assertion to check the result
        assert_eq!(result, 65);
    }
}#[cfg(test)]
mod tests_rug_660 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'A';

        let result: u16 = <char as AsPrimitive<u16>>::as_(p0);

        assert_eq!(result, 65);
    }
}#[cfg(test)]
mod tests_rug_661 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'A';

        <char as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_662 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <char as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_663 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <char as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_664 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'A';

        <char as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_665 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: char = 'A';

        <char as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_666 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'A';

        <char as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_667 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <char as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_668 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'A';

        <char as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_669 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: char = 'A';

        <char as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_670 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: char = 'a';

        <char as AsPrimitive<i128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_671 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        <bool as AsPrimitive<u8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_672 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        <bool as AsPrimitive<u16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_673 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        <bool as AsPrimitive<u32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_674 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        <bool as AsPrimitive<u64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_675 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true; // Using sample data for bool

        <bool as AsPrimitive<usize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_676 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: bool = true;

        <bool as AsPrimitive<u128>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_677 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: bool = true;

        <bool as AsPrimitive<i8>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_678 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        <bool as AsPrimitive<i16>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_679 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: bool = true;

        <bool as AsPrimitive<i32>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_680 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        <bool as AsPrimitive<i64>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_681 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let p0: bool = true; // Using sample data for bool type

        <bool as AsPrimitive<isize>>::as_(p0);
    }
}#[cfg(test)]
mod tests_rug_682 {
    use super::*;
    use crate::AsPrimitive;

    #[test]
    fn test_rug() {
        let mut p0: bool = true;

        <bool as AsPrimitive<i128>>::as_(p0);
    }
}