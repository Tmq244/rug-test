//! Traits input types have to implement to work with nom combinators
use crate::error::{ErrorKind, ParseError};
use crate::internal::{Err, IResult, Needed};
use crate::lib::std::iter::{Copied, Enumerate};
use crate::lib::std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use crate::lib::std::slice::Iter;
use crate::lib::std::str::from_utf8;
use crate::lib::std::str::CharIndices;
use crate::lib::std::str::Chars;
use crate::lib::std::str::FromStr;

#[cfg(feature = "alloc")]
use crate::lib::std::string::String;
#[cfg(feature = "alloc")]
use crate::lib::std::vec::Vec;

/// Abstract method to calculate the input length
pub trait InputLength {
  /// Calculates the input length, as indicated by its name,
  /// and the name of the trait itself
  fn input_len(&self) -> usize;
}

impl<'a, T> InputLength for &'a [T] {
  #[inline]
  fn input_len(&self) -> usize {
    self.len()
  }
}

impl<'a> InputLength for &'a str {
  #[inline]
  fn input_len(&self) -> usize {
    self.len()
  }
}

impl<'a> InputLength for (&'a [u8], usize) {
  #[inline]
  fn input_len(&self) -> usize {
    //println!("bit input length for ({:?}, {}):", self.0, self.1);
    //println!("-> {}", self.0.len() * 8 - self.1);
    self.0.len() * 8 - self.1
  }
}

/// Useful functions to calculate the offset between slices and show a hexdump of a slice
pub trait Offset {
  /// Offset between the first byte of self and the first byte of the argument
  fn offset(&self, second: &Self) -> usize;
}

impl Offset for [u8] {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

impl<'a> Offset for &'a [u8] {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

impl Offset for str {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

impl<'a> Offset for &'a str {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.as_ptr();
    let snd = second.as_ptr();

    snd as usize - fst as usize
  }
}

/// Helper trait for types that can be viewed as a byte slice
pub trait AsBytes {
  /// Casts the input type to a byte slice
  fn as_bytes(&self) -> &[u8];
}

impl<'a> AsBytes for &'a str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    (*self).as_bytes()
  }
}

impl AsBytes for str {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    self.as_ref()
  }
}

impl<'a> AsBytes for &'a [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    *self
  }
}

impl AsBytes for [u8] {
  #[inline(always)]
  fn as_bytes(&self) -> &[u8] {
    self
  }
}

macro_rules! as_bytes_array_impls {
  ($($N:expr)+) => {
    $(
      impl<'a> AsBytes for &'a [u8; $N] {
        #[inline(always)]
        fn as_bytes(&self) -> &[u8] {
          *self
        }
      }

      impl AsBytes for [u8; $N] {
        #[inline(always)]
        fn as_bytes(&self) -> &[u8] {
          self
        }
      }
    )+
  };
}

as_bytes_array_impls! {
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}

/// Transforms common types to a char for basic token parsing
pub trait AsChar {
  /// makes a char from self
  fn as_char(self) -> char;

  /// Tests that self is an alphabetic character
  ///
  /// Warning: for `&str` it recognizes alphabetic
  /// characters outside of the 52 ASCII letters
  fn is_alpha(self) -> bool;

  /// Tests that self is an alphabetic character
  /// or a decimal digit
  fn is_alphanum(self) -> bool;
  /// Tests that self is a decimal digit
  fn is_dec_digit(self) -> bool;
  /// Tests that self is an hex digit
  fn is_hex_digit(self) -> bool;
  /// Tests that self is an octal digit
  fn is_oct_digit(self) -> bool;
  /// Gets the len in bytes for self
  fn len(self) -> usize;
}

impl AsChar for u8 {
  #[inline]
  fn as_char(self) -> char {
    self as char
  }
  #[inline]
  fn is_alpha(self) -> bool {
    (self >= 0x41 && self <= 0x5A) || (self >= 0x61 && self <= 0x7A)
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    self >= 0x30 && self <= 0x39
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    (self >= 0x30 && self <= 0x39)
      || (self >= 0x41 && self <= 0x46)
      || (self >= 0x61 && self <= 0x66)
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    self >= 0x30 && self <= 0x37
  }
  #[inline]
  fn len(self) -> usize {
    1
  }
}
impl<'a> AsChar for &'a u8 {
  #[inline]
  fn as_char(self) -> char {
    *self as char
  }
  #[inline]
  fn is_alpha(self) -> bool {
    (*self >= 0x41 && *self <= 0x5A) || (*self >= 0x61 && *self <= 0x7A)
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    *self >= 0x30 && *self <= 0x39
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    (*self >= 0x30 && *self <= 0x39)
      || (*self >= 0x41 && *self <= 0x46)
      || (*self >= 0x61 && *self <= 0x66)
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    *self >= 0x30 && *self <= 0x37
  }
  #[inline]
  fn len(self) -> usize {
    1
  }
}

impl AsChar for char {
  #[inline]
  fn as_char(self) -> char {
    self
  }
  #[inline]
  fn is_alpha(self) -> bool {
    self.is_ascii_alphabetic()
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    self.is_ascii_digit()
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    self.is_ascii_hexdigit()
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    self.is_digit(8)
  }
  #[inline]
  fn len(self) -> usize {
    self.len_utf8()
  }
}

impl<'a> AsChar for &'a char {
  #[inline]
  fn as_char(self) -> char {
    *self
  }
  #[inline]
  fn is_alpha(self) -> bool {
    self.is_ascii_alphabetic()
  }
  #[inline]
  fn is_alphanum(self) -> bool {
    self.is_alpha() || self.is_dec_digit()
  }
  #[inline]
  fn is_dec_digit(self) -> bool {
    self.is_ascii_digit()
  }
  #[inline]
  fn is_hex_digit(self) -> bool {
    self.is_ascii_hexdigit()
  }
  #[inline]
  fn is_oct_digit(self) -> bool {
    self.is_digit(8)
  }
  #[inline]
  fn len(self) -> usize {
    self.len_utf8()
  }
}

/// Abstracts common iteration operations on the input type
pub trait InputIter {
  /// The current input type is a sequence of that `Item` type.
  ///
  /// Example: `u8` for `&[u8]` or `char` for `&str`
  type Item;
  /// An iterator over the input type, producing the item and its position
  /// for use with [Slice]. If we're iterating over `&str`, the position
  /// corresponds to the byte index of the character
  type Iter: Iterator<Item = (usize, Self::Item)>;

  /// An iterator over the input type, producing the item
  type IterElem: Iterator<Item = Self::Item>;

  /// Returns an iterator over the elements and their byte offsets
  fn iter_indices(&self) -> Self::Iter;
  /// Returns an iterator over the elements
  fn iter_elements(&self) -> Self::IterElem;
  /// Finds the byte position of the element
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool;
  /// Get the byte offset from the element's position in the stream
  fn slice_index(&self, count: usize) -> Result<usize, Needed>;
}

/// Abstracts slicing operations
pub trait InputTake: Sized {
  /// Returns a slice of `count` bytes. panics if count > length
  fn take(&self, count: usize) -> Self;
  /// Split the stream at the `count` byte offset. panics if count > length
  fn take_split(&self, count: usize) -> (Self, Self);
}

impl<'a> InputIter for &'a [u8] {
  type Item = u8;
  type Iter = Enumerate<Self::IterElem>;
  type IterElem = Copied<Iter<'a, u8>>;

  #[inline]
  fn iter_indices(&self) -> Self::Iter {
    self.iter_elements().enumerate()
  }
  #[inline]
  fn iter_elements(&self) -> Self::IterElem {
    self.iter().copied()
  }
  #[inline]
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool,
  {
    self.iter().position(|b| predicate(*b))
  }
  #[inline]
  fn slice_index(&self, count: usize) -> Result<usize, Needed> {
    if self.len() >= count {
      Ok(count)
    } else {
      Err(Needed::new(count - self.len()))
    }
  }
}

impl<'a> InputTake for &'a [u8] {
  #[inline]
  fn take(&self, count: usize) -> Self {
    &self[0..count]
  }
  #[inline]
  fn take_split(&self, count: usize) -> (Self, Self) {
    let (prefix, suffix) = self.split_at(count);
    (suffix, prefix)
  }
}

impl<'a> InputIter for &'a str {
  type Item = char;
  type Iter = CharIndices<'a>;
  type IterElem = Chars<'a>;
  #[inline]
  fn iter_indices(&self) -> Self::Iter {
    self.char_indices()
  }
  #[inline]
  fn iter_elements(&self) -> Self::IterElem {
    self.chars()
  }
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool,
  {
    for (o, c) in self.char_indices() {
      if predicate(c) {
        return Some(o);
      }
    }
    None
  }
  #[inline]
  fn slice_index(&self, count: usize) -> Result<usize, Needed> {
    let mut cnt = 0;
    for (index, _) in self.char_indices() {
      if cnt == count {
        return Ok(index);
      }
      cnt += 1;
    }
    if cnt == count {
      return Ok(self.len());
    }
    Err(Needed::Unknown)
  }
}

impl<'a> InputTake for &'a str {
  #[inline]
  fn take(&self, count: usize) -> Self {
    &self[..count]
  }

  // return byte index
  #[inline]
  fn take_split(&self, count: usize) -> (Self, Self) {
    let (prefix, suffix) = self.split_at(count);
    (suffix, prefix)
  }
}

/// Dummy trait used for default implementations (currently only used for `InputTakeAtPosition` and `Compare`).
///
/// When implementing a custom input type, it is possible to use directly the
/// default implementation: If the input type implements `InputLength`, `InputIter`,
/// `InputTake` and `Clone`, you can implement `UnspecializedInput` and get
/// a default version of `InputTakeAtPosition` and `Compare`.
///
/// For performance reasons, you might want to write a custom implementation of
/// `InputTakeAtPosition` (like the one for `&[u8]`).
pub trait UnspecializedInput {}

/// Methods to take as much input as possible until the provided function returns true for the current element.
///
/// A large part of nom's basic parsers are built using this trait.
pub trait InputTakeAtPosition: Sized {
  /// The current input type is a sequence of that `Item` type.
  ///
  /// Example: `u8` for `&[u8]` or `char` for `&str`
  type Item;

  /// Looks for the first element of the input type for which the condition returns true,
  /// and returns the input up to this position.
  ///
  /// *streaming version*: If no element is found matching the condition, this will return `Incomplete`
  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;

  /// Looks for the first element of the input type for which the condition returns true
  /// and returns the input up to this position.
  ///
  /// Fails if the produced slice is empty.
  ///
  /// *streaming version*: If no element is found matching the condition, this will return `Incomplete`
  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;

  /// Looks for the first element of the input type for which the condition returns true,
  /// and returns the input up to this position.
  ///
  /// *complete version*: If no element is found matching the condition, this will return the whole input
  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;

  /// Looks for the first element of the input type for which the condition returns true
  /// and returns the input up to this position.
  ///
  /// Fails if the produced slice is empty.
  ///
  /// *complete version*: If no element is found matching the condition, this will return the whole input
  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool;
}

impl<T: InputLength + InputIter + InputTake + Clone + UnspecializedInput> InputTakeAtPosition
  for T
{
  type Item = <T as InputIter>::Item;

  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.position(predicate) {
      Some(n) => Ok(self.take_split(n)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.position(predicate) {
      Some(0) => Err(Err::Error(E::from_error_kind(self.clone(), e))),
      Some(n) => Ok(self.take_split(n)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.split_at_position(predicate) {
      Err(Err::Incomplete(_)) => Ok(self.take_split(self.input_len())),
      res => res,
    }
  }

  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.split_at_position1(predicate, e) {
      Err(Err::Incomplete(_)) => {
        if self.input_len() == 0 {
          Err(Err::Error(E::from_error_kind(self.clone(), e)))
        } else {
          Ok(self.take_split(self.input_len()))
        }
      }
      res => res,
    }
  }
}

impl<'a> InputTakeAtPosition for &'a [u8] {
  type Item = u8;

  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(i) => Ok(self.take_split(i)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      Some(i) => Ok(self.take_split(i)),
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(i) => Ok(self.take_split(i)),
      None => Ok(self.take_split(self.input_len())),
    }
  }

  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.iter().position(|c| predicate(*c)) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      Some(i) => Ok(self.take_split(i)),
      None => {
        if self.is_empty() {
          Err(Err::Error(E::from_error_kind(self, e)))
        } else {
          Ok(self.take_split(self.input_len()))
        }
      }
    }
  }
}

impl<'a> InputTakeAtPosition for &'a str {
  type Item = char;

  fn split_at_position<P, E: ParseError<Self>>(&self, predicate: P) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position1<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      None => Err(Err::Incomplete(Needed::new(1))),
    }
  }

  fn split_at_position_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      // the end of slice is a char boundary
      None => unsafe {
        Ok((
          self.get_unchecked(self.len()..),
          self.get_unchecked(..self.len()),
        ))
      },
    }
  }

  fn split_at_position1_complete<P, E: ParseError<Self>>(
    &self,
    predicate: P,
    e: ErrorKind,
  ) -> IResult<Self, Self, E>
  where
    P: Fn(Self::Item) -> bool,
  {
    match self.find(predicate) {
      Some(0) => Err(Err::Error(E::from_error_kind(self, e))),
      // find() returns a byte index that is already in the slice at a char boundary
      Some(i) => unsafe { Ok((self.get_unchecked(i..), self.get_unchecked(..i))) },
      None => {
        if self.is_empty() {
          Err(Err::Error(E::from_error_kind(self, e)))
        } else {
          // the end of slice is a char boundary
          unsafe {
            Ok((
              self.get_unchecked(self.len()..),
              self.get_unchecked(..self.len()),
            ))
          }
        }
      }
    }
  }
}

/// Indicates whether a comparison was successful, an error, or
/// if more data was needed
#[derive(Debug, PartialEq)]
pub enum CompareResult {
  /// Comparison was successful
  Ok,
  /// We need more data to be sure
  Incomplete,
  /// Comparison failed
  Error,
}

/// Abstracts comparison operations
pub trait Compare<T> {
  /// Compares self to another value for equality
  fn compare(&self, t: T) -> CompareResult;
  /// Compares self to another value for equality
  /// independently of the case.
  ///
  /// Warning: for `&str`, the comparison is done
  /// by lowercasing both strings and comparing
  /// the result. This is a temporary solution until
  /// a better one appears
  fn compare_no_case(&self, t: T) -> CompareResult;
}

fn lowercase_byte(c: u8) -> u8 {
  match c {
    b'A'..=b'Z' => c - b'A' + b'a',
    _ => c,
  }
}

impl<'a, 'b> Compare<&'b [u8]> for &'a [u8] {
  #[inline(always)]
  fn compare(&self, t: &'b [u8]) -> CompareResult {
    let pos = self.iter().zip(t.iter()).position(|(a, b)| a != b);

    match pos {
      Some(_) => CompareResult::Error,
      None => {
        if self.len() >= t.len() {
          CompareResult::Ok
        } else {
          CompareResult::Incomplete
        }
      }
    }

    /*
    let len = self.len();
    let blen = t.len();
    let m = if len < blen { len } else { blen };
    let reduced = &self[..m];
    let b = &t[..m];

    if reduced != b {
      CompareResult::Error
    } else if m < blen {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
    */
  }

  #[inline(always)]
  fn compare_no_case(&self, t: &'b [u8]) -> CompareResult {
    if self
      .iter()
      .zip(t)
      .any(|(a, b)| lowercase_byte(*a) != lowercase_byte(*b))
    {
      CompareResult::Error
    } else if self.len() < t.len() {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
  }
}

impl<
    T: InputLength + InputIter<Item = u8> + InputTake + UnspecializedInput,
    O: InputLength + InputIter<Item = u8> + InputTake,
  > Compare<O> for T
{
  #[inline(always)]
  fn compare(&self, t: O) -> CompareResult {
    let pos = self
      .iter_elements()
      .zip(t.iter_elements())
      .position(|(a, b)| a != b);

    match pos {
      Some(_) => CompareResult::Error,
      None => {
        if self.input_len() >= t.input_len() {
          CompareResult::Ok
        } else {
          CompareResult::Incomplete
        }
      }
    }
  }

  #[inline(always)]
  fn compare_no_case(&self, t: O) -> CompareResult {
    if self
      .iter_elements()
      .zip(t.iter_elements())
      .any(|(a, b)| lowercase_byte(a) != lowercase_byte(b))
    {
      CompareResult::Error
    } else if self.input_len() < t.input_len() {
      CompareResult::Incomplete
    } else {
      CompareResult::Ok
    }
  }
}

impl<'a, 'b> Compare<&'b str> for &'a [u8] {
  #[inline(always)]
  fn compare(&self, t: &'b str) -> CompareResult {
    self.compare(AsBytes::as_bytes(t))
  }
  #[inline(always)]
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    self.compare_no_case(AsBytes::as_bytes(t))
  }
}

impl<'a, 'b> Compare<&'b str> for &'a str {
  #[inline(always)]
  fn compare(&self, t: &'b str) -> CompareResult {
    self.as_bytes().compare(t.as_bytes())
  }

  //FIXME: this version is too simple and does not use the current locale
  #[inline(always)]
  fn compare_no_case(&self, t: &'b str) -> CompareResult {
    let pos = self
      .chars()
      .zip(t.chars())
      .position(|(a, b)| a.to_lowercase().ne(b.to_lowercase()));

    match pos {
      Some(_) => CompareResult::Error,
      None => {
        if self.len() >= t.len() {
          CompareResult::Ok
        } else {
          CompareResult::Incomplete
        }
      }
    }
  }
}

impl<'a, 'b> Compare<&'b [u8]> for &'a str {
  #[inline(always)]
  fn compare(&self, t: &'b [u8]) -> CompareResult {
    AsBytes::as_bytes(self).compare(t)
  }
  #[inline(always)]
  fn compare_no_case(&self, t: &'b [u8]) -> CompareResult {
    AsBytes::as_bytes(self).compare_no_case(t)
  }
}

/// Look for a token in self
pub trait FindToken<T> {
  /// Returns true if self contains the token
  fn find_token(&self, token: T) -> bool;
}

impl<'a> FindToken<u8> for &'a [u8] {
  fn find_token(&self, token: u8) -> bool {
    memchr::memchr(token, self).is_some()
  }
}

impl<'a> FindToken<u8> for &'a str {
  fn find_token(&self, token: u8) -> bool {
    self.as_bytes().find_token(token)
  }
}

impl<'a, 'b> FindToken<&'a u8> for &'b [u8] {
  fn find_token(&self, token: &u8) -> bool {
    self.find_token(*token)
  }
}

impl<'a, 'b> FindToken<&'a u8> for &'b str {
  fn find_token(&self, token: &u8) -> bool {
    self.as_bytes().find_token(token)
  }
}

impl<'a> FindToken<char> for &'a [u8] {
  fn find_token(&self, token: char) -> bool {
    self.iter().any(|i| *i == token as u8)
  }
}

impl<'a> FindToken<char> for &'a str {
  fn find_token(&self, token: char) -> bool {
    self.chars().any(|i| i == token)
  }
}

impl<'a> FindToken<char> for &'a [char] {
  fn find_token(&self, token: char) -> bool {
    self.iter().any(|i| *i == token)
  }
}

impl<'a, 'b> FindToken<&'a char> for &'b [char] {
  fn find_token(&self, token: &char) -> bool {
    self.find_token(*token)
  }
}

/// Look for a substring in self
pub trait FindSubstring<T> {
  /// Returns the byte position of the substring if it is found
  fn find_substring(&self, substr: T) -> Option<usize>;
}

impl<'a, 'b> FindSubstring<&'b [u8]> for &'a [u8] {
  fn find_substring(&self, substr: &'b [u8]) -> Option<usize> {
    if substr.len() > self.len() {
      return None;
    }

    let (&substr_first, substr_rest) = match substr.split_first() {
      Some(split) => split,
      // an empty substring is found at position 0
      // This matches the behavior of str.find("").
      None => return Some(0),
    };

    if substr_rest.is_empty() {
      return memchr::memchr(substr_first, self);
    }

    let mut offset = 0;
    let haystack = &self[..self.len() - substr_rest.len()];

    while let Some(position) = memchr::memchr(substr_first, &haystack[offset..]) {
      offset += position;
      let next_offset = offset + 1;
      if &self[next_offset..][..substr_rest.len()] == substr_rest {
        return Some(offset);
      }

      offset = next_offset;
    }

    None
  }
}

impl<'a, 'b> FindSubstring<&'b str> for &'a [u8] {
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find_substring(AsBytes::as_bytes(substr))
  }
}

impl<'a, 'b> FindSubstring<&'b str> for &'a str {
  //returns byte index
  fn find_substring(&self, substr: &'b str) -> Option<usize> {
    self.find(substr)
  }
}

/// Used to integrate `str`'s `parse()` method
pub trait ParseTo<R> {
  /// Succeeds if `parse()` succeeded. The byte slice implementation
  /// will first convert it to a `&str`, then apply the `parse()` function
  fn parse_to(&self) -> Option<R>;
}

impl<'a, R: FromStr> ParseTo<R> for &'a [u8] {
  fn parse_to(&self) -> Option<R> {
    from_utf8(self).ok().and_then(|s| s.parse().ok())
  }
}

impl<'a, R: FromStr> ParseTo<R> for &'a str {
  fn parse_to(&self) -> Option<R> {
    self.parse().ok()
  }
}

/// Slicing operations using ranges.
///
/// This trait is loosely based on
/// `Index`, but can actually return
/// something else than a `&[T]` or `&str`
pub trait Slice<R> {
  /// Slices self according to the range argument
  fn slice(&self, range: R) -> Self;
}

macro_rules! impl_fn_slice {
  ( $ty:ty ) => {
    fn slice(&self, range: $ty) -> Self {
      &self[range]
    }
  };
}

macro_rules! slice_range_impl {
  ( [ $for_type:ident ], $ty:ty ) => {
    impl<'a, $for_type> Slice<$ty> for &'a [$for_type] {
      impl_fn_slice!($ty);
    }
  };
  ( $for_type:ty, $ty:ty ) => {
    impl<'a> Slice<$ty> for &'a $for_type {
      impl_fn_slice!($ty);
    }
  };
}

macro_rules! slice_ranges_impl {
  ( [ $for_type:ident ] ) => {
    slice_range_impl! {[$for_type], Range<usize>}
    slice_range_impl! {[$for_type], RangeTo<usize>}
    slice_range_impl! {[$for_type], RangeFrom<usize>}
    slice_range_impl! {[$for_type], RangeFull}
  };
  ( $for_type:ty ) => {
    slice_range_impl! {$for_type, Range<usize>}
    slice_range_impl! {$for_type, RangeTo<usize>}
    slice_range_impl! {$for_type, RangeFrom<usize>}
    slice_range_impl! {$for_type, RangeFull}
  };
}

slice_ranges_impl! {str}
slice_ranges_impl! {[T]}

macro_rules! array_impls {
  ($($N:expr)+) => {
    $(
      impl InputLength for [u8; $N] {
        #[inline]
        fn input_len(&self) -> usize {
          self.len()
        }
      }

      impl<'a> InputLength for &'a [u8; $N] {
        #[inline]
        fn input_len(&self) -> usize {
          self.len()
        }
      }

      impl<'a> InputIter for &'a [u8; $N] {
        type Item = u8;
        type Iter = Enumerate<Self::IterElem>;
        type IterElem = Copied<Iter<'a, u8>>;

        fn iter_indices(&self) -> Self::Iter {
          (&self[..]).iter_indices()
        }

        fn iter_elements(&self) -> Self::IterElem {
          (&self[..]).iter_elements()
        }

        fn position<P>(&self, predicate: P) -> Option<usize>
          where P: Fn(Self::Item) -> bool {
          (&self[..]).position(predicate)
        }

        fn slice_index(&self, count: usize) -> Result<usize, Needed> {
          (&self[..]).slice_index(count)
        }
      }

      impl<'a> Compare<[u8; $N]> for &'a [u8] {
        #[inline(always)]
        fn compare(&self, t: [u8; $N]) -> CompareResult {
          self.compare(&t[..])
        }

        #[inline(always)]
        fn compare_no_case(&self, t: [u8;$N]) -> CompareResult {
          self.compare_no_case(&t[..])
        }
      }

      impl<'a,'b> Compare<&'b [u8; $N]> for &'a [u8] {
        #[inline(always)]
        fn compare(&self, t: &'b [u8; $N]) -> CompareResult {
          self.compare(&t[..])
        }

        #[inline(always)]
        fn compare_no_case(&self, t: &'b [u8;$N]) -> CompareResult {
          self.compare_no_case(&t[..])
        }
      }

      impl FindToken<u8> for [u8; $N] {
        fn find_token(&self, token: u8) -> bool {
          memchr::memchr(token, &self[..]).is_some()
        }
      }

      impl<'a> FindToken<&'a u8> for [u8; $N] {
        fn find_token(&self, token: &u8) -> bool {
          self.find_token(*token)
        }
      }
    )+
  };
}

array_impls! {
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}

/// Abstracts something which can extend an `Extend`.
/// Used to build modified input slices in `escaped_transform`
pub trait ExtendInto {
  /// The current input type is a sequence of that `Item` type.
  ///
  /// Example: `u8` for `&[u8]` or `char` for `&str`
  type Item;

  /// The type that will be produced
  type Extender;

  /// Create a new `Extend` of the correct type
  fn new_builder(&self) -> Self::Extender;
  /// Accumulate the input into an accumulator
  fn extend_into(&self, acc: &mut Self::Extender);
}

#[cfg(feature = "alloc")]
impl ExtendInto for [u8] {
  type Item = u8;
  type Extender = Vec<u8>;

  #[inline]
  fn new_builder(&self) -> Vec<u8> {
    Vec::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut Vec<u8>) {
    acc.extend(self.iter().cloned());
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for &[u8] {
  type Item = u8;
  type Extender = Vec<u8>;

  #[inline]
  fn new_builder(&self) -> Vec<u8> {
    Vec::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut Vec<u8>) {
    acc.extend_from_slice(self);
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for str {
  type Item = char;
  type Extender = String;

  #[inline]
  fn new_builder(&self) -> String {
    String::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut String) {
    acc.push_str(self);
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for &str {
  type Item = char;
  type Extender = String;

  #[inline]
  fn new_builder(&self) -> String {
    String::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut String) {
    acc.push_str(self);
  }
}

#[cfg(feature = "alloc")]
impl ExtendInto for char {
  type Item = char;
  type Extender = String;

  #[inline]
  fn new_builder(&self) -> String {
    String::new()
  }
  #[inline]
  fn extend_into(&self, acc: &mut String) {
    acc.push(*self);
  }
}

/// Helper trait to convert numbers to usize.
///
/// By default, usize implements `From<u8>` and `From<u16>` but not
/// `From<u32>` and `From<u64>` because that would be invalid on some
/// platforms. This trait implements the conversion for platforms
/// with 32 and 64 bits pointer platforms
pub trait ToUsize {
  /// converts self to usize
  fn to_usize(&self) -> usize;
}

impl ToUsize for u8 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

impl ToUsize for u16 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

impl ToUsize for usize {
  #[inline]
  fn to_usize(&self) -> usize {
    *self
  }
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl ToUsize for u32 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

#[cfg(target_pointer_width = "64")]
impl ToUsize for u64 {
  #[inline]
  fn to_usize(&self) -> usize {
    *self as usize
  }
}

/// Equivalent From implementation to avoid orphan rules in bits parsers
pub trait ErrorConvert<E> {
  /// Transform to another error type
  fn convert(self) -> E;
}

impl<I> ErrorConvert<(I, ErrorKind)> for ((I, usize), ErrorKind) {
  fn convert(self) -> (I, ErrorKind) {
    ((self.0).0, self.1)
  }
}

impl<I> ErrorConvert<((I, usize), ErrorKind)> for (I, ErrorKind) {
  fn convert(self) -> ((I, usize), ErrorKind) {
    ((self.0, 0), self.1)
  }
}

use crate::error;
impl<I> ErrorConvert<error::Error<I>> for error::Error<(I, usize)> {
  fn convert(self) -> error::Error<I> {
    error::Error {
      input: self.input.0,
      code: self.code,
    }
  }
}

impl<I> ErrorConvert<error::Error<(I, usize)>> for error::Error<I> {
  fn convert(self) -> error::Error<(I, usize)> {
    error::Error {
      input: (self.input, 0),
      code: self.code,
    }
  }
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
impl<I> ErrorConvert<error::VerboseError<I>> for error::VerboseError<(I, usize)> {
  fn convert(self) -> error::VerboseError<I> {
    error::VerboseError {
      errors: self.errors.into_iter().map(|(i, e)| (i.0, e)).collect(),
    }
  }
}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "alloc")))]
impl<I> ErrorConvert<error::VerboseError<(I, usize)>> for error::VerboseError<I> {
  fn convert(self) -> error::VerboseError<(I, usize)> {
    error::VerboseError {
      errors: self.errors.into_iter().map(|(i, e)| ((i, 0), e)).collect(),
    }
  }
}

impl ErrorConvert<()> for () {
  fn convert(self) {}
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "std")))]
/// Helper trait to show a byte slice as a hex dump
pub trait HexDisplay {
  /// Converts the value of `self` to a hex dump, returning the owned
  /// `String`.
  fn to_hex(&self, chunk_size: usize) -> String;

  /// Converts the value of `self` to a hex dump beginning at `from` address, returning the owned
  /// `String`.
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String;
}

#[cfg(feature = "std")]
static CHARS: &[u8] = b"0123456789abcdef";

#[cfg(feature = "std")]
impl HexDisplay for [u8] {
  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    let mut v = Vec::with_capacity(self.len() * 3);
    let mut i = from;
    for chunk in self.chunks(chunk_size) {
      let s = format!("{:08x}", i);
      for &ch in s.as_bytes().iter() {
        v.push(ch);
      }
      v.push(b'\t');

      i += chunk_size;

      for &byte in chunk {
        v.push(CHARS[(byte >> 4) as usize]);
        v.push(CHARS[(byte & 0xf) as usize]);
        v.push(b' ');
      }
      if chunk_size > chunk.len() {
        for j in 0..(chunk_size - chunk.len()) {
          v.push(b' ');
          v.push(b' ');
          v.push(b' ');
        }
      }
      v.push(b'\t');

      for &byte in chunk {
        if (byte >= 32 && byte <= 126) || byte >= 128 {
          v.push(byte);
        } else {
          v.push(b'.');
        }
      }
      v.push(b'\n');
    }

    String::from_utf8_lossy(&v[..]).into_owned()
  }
}

#[cfg(feature = "std")]
impl HexDisplay for str {
  #[allow(unused_variables)]
  fn to_hex(&self, chunk_size: usize) -> String {
    self.to_hex_from(chunk_size, 0)
  }

  #[allow(unused_variables)]
  fn to_hex_from(&self, chunk_size: usize, from: usize) -> String {
    self.as_bytes().to_hex_from(chunk_size, from)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_offset_u8() {
    let s = b"abcd123";
    let a = &s[..];
    let b = &a[2..];
    let c = &a[..4];
    let d = &a[3..5];
    assert_eq!(a.offset(b), 2);
    assert_eq!(a.offset(c), 0);
    assert_eq!(a.offset(d), 3);
  }

  #[test]
  fn test_offset_str() {
    let s = "abcřèÂßÇd123";
    let a = &s[..];
    let b = &a[7..];
    let c = &a[..5];
    let d = &a[5..9];
    assert_eq!(a.offset(b), 7);
    assert_eq!(a.offset(c), 0);
    assert_eq!(a.offset(d), 5);
  }
}
#[cfg(test)]
mod tests_rug_138 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: u8 = b'A';

        crate::traits::lowercase_byte(p0);
    }
}#[cfg(test)]
mod tests_rug_139 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut v88: [i32; 4] = [1, 2, 3, 4];
        let p0: &[i32] = &v88;

        assert_eq!(p0.input_len(), 4);
    }
}#[cfg(test)]
mod tests_rug_140 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &str = "sample string";

        assert_eq!(p0.input_len(), 13);
    }
}#[cfg(test)]
mod tests_rug_141 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: (&[u8], usize) = (b"sample data", 42);

        assert_eq!(<(&[u8], usize) as InputLength>::input_len(&p0), b"sample data".len() * 8 - 42);
    }
}#[cfg(test)]
mod tests_rug_142 {
    use super::*;
    use crate::Offset;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: &[u8] = b"world";

        <[u8] as Offset>::offset(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_143 {
    use super::*;
    use crate::Offset;

    #[test]
    fn test_rug() {
        let data1: &[u8] = b"hello";
        let data2: &[u8] = &data1[2..]; // This is a sample way to create a second slice that starts after the first two bytes of data1

        let p0: &&[u8] = &data1;
        let p1: &&[u8] = &data2;

        <&[u8] as Offset>::offset(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_144 {
    use super::*;
    use crate::Offset;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello";
        let mut p1: &str = "world";

        <str>::offset(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_145 {
    use super::*;
    use crate::Offset;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello";
        let mut p1: &str = "world";

        p0.offset(p1);
    }
}#[cfg(test)]
mod tests_rug_146 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &str = "sample string";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_147 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &str = "sample string";

        <str>::as_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_148 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"sample data";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_149 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";

        <[u8] as AsBytes>::as_bytes(p0);
    }
}#[cfg(test)]
mod tests_rug_150 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 0] = &[];

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_151 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 0] = [];

        <[u8; 0] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_152 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 1] = &[42];

        <&[u8; 1] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_153 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 1] = [42];

        <[u8; 1] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_154 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 2] = &[1, 2];

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_155 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 2] = [42, 24];

        <[u8; 2] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_156 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 3] = &[1, 2, 3];

        <&[u8; 3] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_157 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 3] = [1, 2, 3];

        <[u8; 3] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_158 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 4] = b"test";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_159 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 4] = [1, 2, 3, 4];

        <[u8; 4] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_160 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 5] = b"hello";

        <&[u8; 5] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_161 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 5] = [1, 2, 3, 4, 5];

        <[u8; 5] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_162 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 6] = b"abcdef";

        <&[u8; 6] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_163 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 6] = [1, 2, 3, 4, 5, 6];

        <[u8; 6] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_164 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 7] = b"abcdefg";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_165 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];

        <[u8; 7] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_166 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 8] = &[1, 2, 3, 4, 5, 6, 7, 8];

        <&[u8; 8] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_167 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

        <[u8; 8] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_168 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 9] = b"123456789";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_169 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 9] = [1, 2, 3, 4, 5, 6, 7, 8, 9];

        <[u8; 9] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_170 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 10] = b"1234567890";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_171 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 10] = [42, 73, 0, 99, 101, 114, 116, 255, 2, 19];

        <[u8; 10] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_172 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 11] = b"hello_world";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_173 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 11] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A];

        <[u8; 11] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_174 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 12] = b"Hello, world";

        <&[u8; 12] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_175 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 12] = [42, 53, 64, 75, 86, 97, 108, 119, 130, 141, 152, 163];

        <[u8; 12] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_176 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let p0: &[u8; 13] = b"Hello, World!";

        <&[u8; 13] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_177 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 13] = [42, 55, 66, 77, 88, 99, 10, 20, 30, 40, 50, 60, 70];

        <[u8; 13] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_178 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 14] = b"Hello, world!!";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_179 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 14] = [42; 14];

        <[u8; 14] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_180 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 15] = b"Hello, World!!!";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_181 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 15] = [42; 15];

        <[u8; 15] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_182 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 16] = b"abcdefghijklmnop";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_183 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 16] = [42; 16];

        <[u8; 16] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_185 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 17] = [42; 17];

        <[u8; 17] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_186 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 18] = &[42; 18];

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_187 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 18] = [42; 18];

        <[u8; 18] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_189 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 19] = [42; 19];

        <[u8; 19] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_190 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 20] = &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x10, 
                                  0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x20];

        <&[u8; 20] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_191 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 20] = [0x1a, 0x2b, 0x3c, 0x4d, 0x5e, 0x6f, 0x7a, 0x8b, 0x9c, 0xad, 0xbe, 0xcf, 0xde, 0xef, 0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5];

        <[u8; 20] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_192 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 21] = &[49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49];

        <&[u8; 21] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_193 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 21] = [42; 21];

        <[u8; 21] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_195 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 22] = [42; 22]; // Sample data to initialize the array

        <[u8; 22] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_196 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 23] = b"12345678901234567890123";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_197 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 23] = [42; 23];

        <[u8; 23] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_198 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 24] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_199 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 24] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];

        <[u8; 24] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_201 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 25] = [42; 25]; // Sample data to initialize the array

        <[u8; 25] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_202 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 26] = b"abcdefghijklmnopqrstuvwxyz";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_203 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 26] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25];

        <[u8; 26] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_205 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 27] = [42; 27];

        <[u8; 27] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_206 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let p0: &[u8; 28] = b"1234567890123456789012345678"; // Sample data to initialize the variable

        <&[u8; 28] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_207 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 28] = [42; 28];

        <[u8; 28] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_208 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 29] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ123";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_209 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 29] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28];

        <[u8; 29] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_211 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 30] = [42; 30];

        <[u8; 30] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_212 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 31] = b"abcdefghijklmnopqrstuvwxyz12345";

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_213 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 31] = [42; 31];

        <[u8; 31] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_214 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 32] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32];

        p0.as_bytes();
    }
}#[cfg(test)]
mod tests_rug_215 {
    use super::*;
    use crate::AsBytes;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [42; 32];

        <[u8; 32] as AsBytes>::as_bytes(&p0);
    }
}#[cfg(test)]
mod tests_rug_216 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 65; // Sample data for u8

        <u8 as AsChar>::as_char(p0);
    }
}#[cfg(test)]
mod tests_rug_217 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'A';

        assert_eq!(<u8 as AsChar>::is_alpha(p0), true);

        p0 = b'z';
        assert_eq!(<u8 as AsChar>::is_alpha(p0), true);

        p0 = b'5';
        assert_eq!(<u8 as AsChar>::is_alpha(p0), false);

        p0 = b'@';
        assert_eq!(<u8 as AsChar>::is_alpha(p0), false);
    }
}#[cfg(test)]
mod tests_rug_218 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'A';

        assert!((<u8 as AsChar>::is_alphanum)(p0));

        p0 = b'1';
        assert!((<u8 as AsChar>::is_alphanum)(p0));

        p0 = b' ';
        assert!(!(<u8 as AsChar>::is_alphanum)(p0));

        p0 = b'z';
        assert!((<u8 as AsChar>::is_alphanum)(p0));

        p0 = b'9';
        assert!((<u8 as AsChar>::is_alphanum)(p0));

        p0 = b'!';
        assert!(!(<u8 as AsChar>::is_alphanum)(p0));
    }
}#[cfg(test)]
mod tests_rug_219 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 53; // Sample data for u8 type

        assert_eq!(<u8 as AsChar>::is_dec_digit(p0), true);

        p0 = 48; // Another sample data for u8 type
        assert_eq!(<u8 as AsChar>::is_dec_digit(p0), true);

        p0 = 39; // Edge case below the range
        assert_eq!(<u8 as AsChar>::is_dec_digit(p0), false);

        p0 = 58; // Edge case above the range
        assert_eq!(<u8 as AsChar>::is_dec_digit(p0), false);
    }
}#[cfg(test)]
mod tests_rug_220 {
    use super::*;
    use crate::traits::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'9'; // Sample data for a hexadecimal digit

        assert!(<u8 as AsChar>::is_hex_digit(p0));

        p0 = b'A'; // Another sample data for a hexadecimal digit
        assert!(<u8 as AsChar>::is_hex_digit(p0));

        p0 = b'a'; // Another sample data for a hexadecimal digit
        assert!(<u8 as AsChar>::is_hex_digit(p0));

        p0 = b'G'; // Non-hexadecimal digit
        assert!(!<u8 as AsChar>::is_hex_digit(p0));

        p0 = b'g'; // Non-hexadecimal digit
        assert!(!<u8 as AsChar>::is_hex_digit(p0));

        p0 = b'0'; // Another sample data for a hexadecimal digit
        assert!(<u8 as AsChar>::is_hex_digit(p0));
    }
}#[cfg(test)]
mod tests_rug_221 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0x34; // Sample octal digit '4'

        assert!(<u8 as AsChar>::is_oct_digit(p0));

        p0 = 0x2F; // Non-octal digit '/'
        assert!(!<u8 as AsChar>::is_oct_digit(p0));

        p0 = 0x37; // Sample octal digit '7'
        assert!(<u8 as AsChar>::is_oct_digit(p0));

        p0 = 0x38; // Non-octal digit '8'
        assert!(!<u8 as AsChar>::is_oct_digit(p0));
    }
}#[cfg(test)]
mod tests_rug_222 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 65; // Sample data for u8

        <u8 as AsChar>::len(p0);
    }
}#[cfg(test)]
mod tests_rug_223 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 65; // Sample data for a u8, ASCII value for 'A'

        <&u8 as AsChar>::as_char(&p0);
    }
}#[cfg(test)]
mod tests_rug_224 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'A';

        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), true);
        
        p0 = b'a';
        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), true);
        
        p0 = b'Z';
        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), true);
        
        p0 = b'z';
        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), true);
        
        p0 = b'0';
        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), false);
        
        p0 = b'9';
        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), false);
        
        p0 = b'@';
        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), false);
        
        p0 = b'[';
        assert_eq!(<&u8 as AsChar>::is_alpha(&p0), false);
    }
}#[cfg(test)]
mod tests_rug_225 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'a';

        <&u8>::is_alphanum(&p0);
    }
}#[cfg(test)]
mod tests_rug_226 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'5'; // Sample data for a decimal digit

        <&u8>::is_dec_digit(&p0);
    }
}#[cfg(test)]
mod tests_rug_227 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'3'; // Sample data for a hex digit

        <&u8 as AsChar>::is_hex_digit(&p0);
    }
}#[cfg(test)]
mod tests_rug_228 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 0x34; // Sample data for a valid octal digit

        <&u8 as AsChar>::is_oct_digit(&p0);
    }
}#[cfg(test)]
mod tests_rug_229 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: u8 = 65; // Sample data for u8

        <&u8 as AsChar>::len(&p0);
    }
}#[cfg(test)]
mod tests_rug_230 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <char as AsChar>::as_char(p0);
    }
}#[cfg(test)]
mod tests_rug_231 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        assert_eq!(<char as AsChar>::is_alpha(p0), true);

        p0 = 'Z';
        assert_eq!(<char as AsChar>::is_alpha(p0), true);

        p0 = '1';
        assert_eq!(<char as AsChar>::is_alpha(p0), false);

        p0 = ' ';
        assert_eq!(<char as AsChar>::is_alpha(p0), false);

        p0 = '\n';
        assert_eq!(<char as AsChar>::is_alpha(p0), false);
    }
}#[cfg(test)]
mod tests_rug_232 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        assert!((<char as AsChar>::is_alphanum)(p0));

        p0 = '9';
        assert!((<char as AsChar>::is_alphanum)(p0));

        p0 = '@';
        assert!(!(<char as AsChar>::is_alphanum)(p0));
    }
}#[cfg(test)]
mod tests_rug_233 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = '5';

        assert_eq!(<char as AsChar>::is_dec_digit(p0), true);

        p0 = 'a';
        assert_eq!(<char as AsChar>::is_dec_digit(p0), false);

        p0 = '9';
        assert_eq!(<char as AsChar>::is_dec_digit(p0), true);

        p0 = ' ';
        assert_eq!(<char as AsChar>::is_dec_digit(p0), false);
    }
}#[cfg(test)]
mod tests_rug_234 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        assert_eq!(<char as AsChar>::is_hex_digit(p0), true);

        p0 = 'F';
        assert_eq!(<char as AsChar>::is_hex_digit(p0), true);

        p0 = '1';
        assert_eq!(<char as AsChar>::is_hex_digit(p0), true);

        p0 = 'G';
        assert_eq!(<char as AsChar>::is_hex_digit(p0), false);

        p0 = 'g';
        assert_eq!(<char as AsChar>::is_hex_digit(p0), true);

        p0 = 'z';
        assert_eq!(<char as AsChar>::is_hex_digit(p0), false);

        p0 = ' ';
        assert_eq!(<char as AsChar>::is_hex_digit(p0), false);
    }
}#[cfg(test)]
mod tests_rug_235 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = '7';

        assert_eq!(<char as AsChar>::is_oct_digit(p0), true);

        p0 = '8';
        assert_eq!(<char as AsChar>::is_oct_digit(p0), false);

        p0 = '0';
        assert_eq!(<char as AsChar>::is_oct_digit(p0), true);

        p0 = '9';
        assert_eq!(<char as AsChar>::is_oct_digit(p0), false);

        p0 = 'a';
        assert_eq!(<char as AsChar>::is_oct_digit(p0), false);
    }
}#[cfg(test)]
mod tests_rug_236 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <char as AsChar>::len(p0);
    }
}#[cfg(test)]
mod tests_rug_237 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <&char>::as_char(&p0);
    }
}#[cfg(test)]
mod tests_rug_238 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <&char>::is_alpha(&p0);
    }
}#[cfg(test)]
mod tests_rug_239 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let p0: char = 'a';

        <&char as AsChar>::is_alphanum(&p0);
    }
}#[cfg(test)]
mod tests_rug_240 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let p0: char = '5';

        <&char>::is_dec_digit(&p0);
    }
}#[cfg(test)]
mod tests_rug_241 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let p0: char = 'a';

        <&char>::is_hex_digit(&p0);
    }
}#[cfg(test)]
mod tests_rug_242 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = '7';

        <&char>::is_oct_digit(&p0);
    }
}#[cfg(test)]
mod tests_rug_243 {
    use super::*;
    use crate::AsChar;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        assert_eq!(p0.len(), 1);
    }
}#[cfg(test)]
mod tests_rug_244 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_245 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_247 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: usize = 3;

        p0.slice_index(p1);
    }
}#[cfg(test)]
mod tests_rug_248 {
    use super::*;
    use crate::InputTake;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello world";
        let mut p1: usize = 5;

        p0.take(p1);
    }
}#[cfg(test)]
mod tests_rug_249 {
    use super::*;
    use crate::InputTake;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello world";
        let mut p1: usize = 5;

        let (suffix, prefix) = p0.take_split(p1);

        assert_eq!(suffix, b"hello");
        assert_eq!(prefix, b" world");
    }
}#[cfg(test)]
mod tests_rug_250 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello, world";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_251 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &'static str = "example";

        <&str as InputIter>::iter_elements(&p0).for_each(|c| println!("{}", c));
    }
}#[cfg(test)]
mod tests_rug_252 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &str = "Hello, world! 😊";
        let c = '😊';
        let mut p1 = c.escape_unicode();

        p0.position(|ch| p1.clone().any(|esc_char| esc_char == ch));
    }
}#[cfg(test)]
mod tests_rug_253 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello world";
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_254 {
    use super::*;
    use crate::InputTake;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello";
        let mut p1: usize = 3;

        p0.take(p1);
    }
}#[cfg(test)]
mod tests_rug_255 {
    use super::*;
    use crate::InputTake;

    #[test]
    fn test_rug() {
        let mut p0: &str = "Hello, world!";
        let mut p1: usize = 5;

        let (suffix, prefix) = p0.take_split(p1);
        
        assert_eq!(prefix, "Hello");
        assert_eq!(suffix, ", world!");
    }
}#[cfg(test)]
mod tests_rug_268 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: &[u8] = b"hello";

        <&[u8] as Compare<&[u8]>>::compare(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_269 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let p0: &[u8] = b"Hello";
        let p1: &[u8] = b"hello";

        assert_eq!(p0.compare_no_case(p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_272 {
    use super::*;
    use crate::Compare;
    
    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: &str = "hello";

        assert_eq!(p0.compare(p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_274 {
    use super::*;
    use crate::traits::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello";
        let mut p1: &str = "world";

        <&str as Compare<&str>>::compare(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_276 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &str = "example";
        let mut p1: &[u8] = b"example";

        assert_eq!(p0.compare(p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_277 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &str = "HelloWorld";
        let mut p1: &[u8] = b"helloworld";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_278 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &'static [u8] = b"hello world";
        let mut p1: u8 = b'o';

        assert_eq!(p0.find_token(p1), true);

        let mut p2: &'static [u8] = b"rustaceans";
        let mut p3: u8 = b'x';

        assert_eq!(p2.find_token(p3), false);
    }
}#[cfg(test)]
mod tests_rug_279 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &str = "example";
        let mut p1: u8 = b'e';

        assert!(p0.find_token(p1));
    }
}#[cfg(test)]
mod tests_rug_280 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello world";
        let mut p1: u8 = b'o';

        assert!(p0.find_token(p1));
    }
}#[cfg(test)]
mod tests_rug_281 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello world";
        let mut p1: u8 = b'w';

        assert!(p0.find_token(&p1));
    }
}#[cfg(test)]
mod tests_rug_282 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: char = 'e';

        assert!(p0.find_token(p1));

        let mut p0: &[u8] = b"world";
        let mut p1: char = 'x';

        assert!(!p0.find_token(p1));
    }
}#[cfg(test)]
mod tests_rug_283 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &str = "example";
        let mut p1: char = 'a';

        assert_eq!(p0.find_token(p1), true);

        p0 = "hello";
        p1 = 'z';
        
        assert_eq!(p0.find_token(p1), false);
    }
}#[cfg(test)]
mod tests_rug_284 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &[char] = &['a', 'b', 'c', 'd'];
        let mut p1: char = 'c';

        assert!(p0.find_token(p1));
    }
}#[cfg(test)]
mod tests_rug_285 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: &[char] = &['a', 'b', 'c', 'd'];
        let mut p1: char = 'c';

        assert_eq!(p0.find_token(&p1), true);
        
        let mut p1: char = 'e';
        assert_eq!(p0.find_token(&p1), false);
    }
}#[cfg(test)]
mod tests_rug_286 {
    use super::*;
    use crate::FindSubstring;

    #[test]
    fn test_rug() {
        let p0: &[u8] = b"hello world";
        let p1: &[u8] = b"world";

        assert_eq!(p0.find_substring(p1), Some(6));
    }
}#[cfg(test)]
mod tests_rug_287 {
    use super::*;
    use crate::FindSubstring;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello world";
        let mut p1: &str = "world";

        assert_eq!(p0.find_substring(p1), Some(6));
    }
}#[cfg(test)]
mod tests_rug_288 {
    use super::*;
    use crate::FindSubstring;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello world";
        let mut p1: &str = "world";

        assert_eq!(p0.find_substring(&p1), Some(6));
    }
}#[cfg(test)]
mod tests_rug_291 {
    use super::*;
    use crate::Slice;
    use std::ops::Range;

    #[test]
    fn test_rug() {
        let mut p0: &str = "Hello, world!";
        let mut p1: Range<usize> = Range { start: 0, end: 10 };

        p0.slice(p1);
    }
}#[cfg(test)]
mod tests_rug_292 {
    use super::*;
    use crate::Slice;
    use std::ops::RangeTo;

    #[test]
    fn test_rug() {
        let mut p0: &'static str = "Hello, world!"; // sample data for &'a str
        let mut p1: RangeTo<usize> = RangeTo { end: 10 }; // using the sample code to construct it

        p0.slice(p1);
    }
}#[cfg(test)]
mod tests_rug_293 {
    use super::*;
    use crate::Slice;
    use std::ops::RangeFrom;

    #[test]
    fn test_rug() {
        let mut p0: &'static str = "Hello, world!";
        let mut p1 = RangeFrom { start: 0 };

        p0.slice(p1);
    }
}#[cfg(test)]
mod tests_rug_294 {
    use super::*;
    use crate::Slice;
    use std::ops::RangeFull;

    #[test]
    fn test_rug() {
        let p0: &'static str = "Hello, world!";
        let p1: RangeFull = std::ops::RangeFull;

        p0.slice(p1);
    }
}#[cfg(test)]
mod tests_rug_295 {
    use super::*;
    use crate::Slice;
    use std::ops::Range;

    #[test]
    fn test_rug() {
        let mut p0: [i32; 4] = [1, 2, 3, 4];
        let mut p1: Range<usize> = Range { start: 0, end: 10 };

        let result = (&p0 as &[i32]).slice(p1);

        assert_eq!(result, &[1, 2, 3, 4]);
    }
}#[cfg(test)]
mod tests_rug_299 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 0] = [];

        <[u8; 0] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_300 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 0] = &[];

        assert_eq!(p0.input_len(), 0);
    }
}#[cfg(test)]
mod tests_rug_301 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 0] = &[];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_302 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 0] = &[];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_304 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 0] = &[];
        let mut p1: usize = 42;

        <&[u8; 0] as InputIter>::slice_index(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_305 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 0] = [];

        assert_eq!(p0.compare(p1), CompareResult::Incomplete);
    }
}#[cfg(test)]
mod tests_rug_306 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 0] = [];

        assert_eq!(p0.compare_no_case(p1), CompareResult::Incomplete);
    }
}#[cfg(test)]
mod tests_rug_307 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"some sample data";
        let mut p1: [u8; 0] = [];

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_308 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 0] = [];

        p0.compare_no_case(&p1);
    }
}#[cfg(test)]
mod tests_rug_309 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 0] = [];
        let mut p1: u8 = b'a';

        <[u8; 0] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_310 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 0] = [];
        let mut p1: &u8 = &b'a';

        <[u8; 0] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_311 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let p0: [u8; 1] = [42];

        <[u8; 1] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_312 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let p0: &[u8; 1] = &[42];

        assert_eq!(p0.input_len(), 1);
    }
}#[cfg(test)]
mod tests_rug_313 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 1] = &[42];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_314 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 1] = &[42];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_315 {
    use super::*;
    use crate::InputIter;
    
    #[test]
    fn test_rug() {
        let mut p0: &[u8; 1] = &[42]; // Sample data for the first argument
        let mut p1: Box<dyn Fn(u8) -> bool> = Box::new(|x| x == 42); // Constructing the second argument based on the sample

        p0.position(p1);
    }
}#[cfg(test)]
mod tests_rug_316 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 1] = &[42];
        let mut p1: usize = 1;

        <&[u8; 1] as InputIter>::slice_index(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_317 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: [u8; 1] = [b'h'];

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_318 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello";
        let mut p1: [u8; 1] = [b'h'];

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_319 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 1] = [b'e'];

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_320 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let p0: &[u8] = b"Hello";
        let p1: [u8; 1] = *b"H";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Incomplete);
    }
}#[cfg(test)]
mod tests_rug_321 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 1] = [42];
        let mut p1: u8 = 42;

        <[u8; 1] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_322 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 1] = [b'a'];
        let mut p1: &u8 = &b'b';

        <[u8; 1] as FindToken<u8>>::find_token(&p0, *p1);
    }
}#[cfg(test)]
mod tests_rug_323 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 2] = [42, 24];

        <[u8; 2] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_324 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 2] = &[1, 2];

        assert_eq!(p0.input_len(), 2);
    }
}#[cfg(test)]
mod tests_rug_325 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 2] = &[1, 2];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_326 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 2] = &[1, 2];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_327 {
    use super::*;
    use crate::InputIter;
    use crate::error::ErrorKind;

    #[test]
    fn test_rug() {
        let p0: &[u8; 2] = b"ab";
        let p1 = |c| c == b'b';

        <&[u8; 2] as InputIter>::position(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_328 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 2] = &[1, 2];
        let mut p1: usize = 1;

        assert_eq!(p0.slice_index(p1), Ok(1));
    }
}#[cfg(test)]
mod tests_rug_329 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcd";
        let mut p1: [u8; 2] = [97, 98]; // 'a' and 'b'

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_330 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Ab";
        let mut p1: [u8; 2] = *b"aB";

        assert_eq!(p0.compare_no_case(p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_331 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: [u8; 2] = [104, 101]; // 'h' and 'e'

        <&[u8] as Compare<&[u8; 2]>>::compare(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_332 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Ab";
        let mut p1: [u8; 2] = *b"aB";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_333 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 2] = [1, 2];
        let mut p1: u8 = 1;

        <[u8; 2] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_334 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 2] = [1, 2];
        let mut p1: &u8 = &1;

        <[u8; 2] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_335 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 3] = [1, 2, 3];

        <[u8; 3] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_336 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let p0: &[u8; 3] = b"abc";

        <&[u8; 3] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_337 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 3] = &[1, 2, 3];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_338 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 3] = &[1, 2, 3];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_340 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 3] = &[1, 2, 3];
        let mut p1: usize = 1;

        assert_eq!(p0.slice_index(p1), Ok(1));
    }
}#[cfg(test)]
mod tests_rug_341 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: [u8; 3] = [104, 101, 108]; // Corresponds to "hel"

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_342 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"AbC";
        let mut p1: [u8; 3] = *b"abc";

        assert_eq!(p0.compare_no_case(p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_343 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abc";
        let mut p1: [u8; 3] = [97, 98, 99];

        <&[u8] as Compare<&[u8; 3]>>::compare(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_344 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello";
        let mut p1: [u8; 3] = *b"hel";

        p0.compare_no_case(&p1);
    }
}#[cfg(test)]
mod tests_rug_345 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 3] = [1, 2, 3];
        let mut p1: u8 = 2;

        <[u8; 3] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_346 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 3] = [1, 2, 3];
        let p1: &u8 = &2;

        <[u8; 3] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_347 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 4] = [1, 2, 3, 4];

        <[u8; 4] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_348 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 4] = &[1, 2, 3, 4];

        assert_eq!(p0.input_len(), 4);
    }
}#[cfg(test)]
mod tests_rug_349 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 4] = &[1, 2, 3, 4];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_350 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 4] = &[1, 2, 3, 4];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_352 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 4] = b"test";
        let mut p1: usize = 2;

        <&[u8; 4] as InputIter>::slice_index(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_353 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"test";
        let mut p1: [u8; 4] = *b"test";

        <&[u8] as Compare<[u8; 4]>>::compare(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_354 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Test";
        let mut p1: [u8; 4] = *b"test";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_355 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: [u8; 4] = [1, 2, 3, 4];

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_356 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 4] = *b"Worl";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Incomplete);
    }
}#[cfg(test)]
mod tests_rug_357 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 4] = [1, 2, 3, 4];
        let mut p1: u8 = 2;

        assert_eq!(&p0.find_token(p1), &true);
        
        let mut p1: u8 = 5;
        assert_eq!(&p0.find_token(p1), &false);
    }
}#[cfg(test)]
mod tests_rug_358 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 4] = [1, 2, 3, 4];
        let mut p1: &u8 = &2;

        <[u8; 4] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_359 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 5] = [1, 2, 3, 4, 5];

        <[u8; 5] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_360 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 5] = &[1, 2, 3, 4, 5];

        assert_eq!(p0.input_len(), 5);
    }
}#[cfg(test)]
mod tests_rug_361 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 5] = b"hello";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_362 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 5] = &[1, 2, 3, 4, 5];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_363 {
    use super::*;
    use crate::InputIter;
    use std::boxed::Box;

    #[test]
    fn test_rug() {
        let p0: &[u8; 5] = b"hello";
        let p1: Box<dyn Fn(u8) -> bool> = Box::new(|x| x == b'o');

        <&[u8; 5] as InputIter>::position(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_364 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 5] = b"hello";
        let mut p1: usize = 3;

        <&[u8; 5] as InputIter>::slice_index(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_365 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello";
        let mut p1: [u8; 5] = *b"world";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_366 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello";
        let mut p1: [u8; 5] = *b"hello";

        assert_eq!(p0.compare_no_case(p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_367 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello world";
        let mut p1: [u8; 5] = *b"hello";

        <&[u8] as Compare<&[u8; 5]>>::compare(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_368 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello";
        let mut p1: [u8; 5] = *b"hello";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_369 {
    use super::*;
    use crate::FindToken;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 5] = [1, 2, 3, 4, 5];
        let mut p1: u8 = 3;

        assert_eq!(<[u8; 5] as FindToken<u8>>::find_token(&p0, p1), true);

        let mut p0: [u8; 5] = [1, 2, 3, 4, 5];
        let mut p1: u8 = 6;

        assert_eq!(<[u8; 5] as FindToken<u8>>::find_token(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_370 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 5] = [1, 2, 3, 4, 5];
        let mut p1: &u8 = &3;

        <[u8; 5] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_371 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 6] = [1, 2, 3, 4, 5, 6];

        <[u8; 6] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_372 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let p0: &[u8; 6] = b"abcdef";

        <&[u8; 6] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_373 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 6] = &[1, 2, 3, 4, 5, 6];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_374 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 6] = &[1, 2, 3, 4, 5, 6];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_376 {
    use super::*;
    use crate::InputIter;
    use crate::Needed;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 6] = b"abcdef";
        let mut p1: usize = 3;

        match <&[u8; 6] as InputIter>::slice_index(&p0, p1) {
            Ok(index) => println!("Index: {}", index),
            Err(needed) => println!("Needed: {:?}", needed),
        }
    }
}#[cfg(test)]
mod tests_rug_377 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdef";
        let mut p1: [u8; 6] = *b"abcdef";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_378 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 6] = *b"exAmPl";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_379 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdef";
        let mut p1: [u8; 6] = *b"abcdef";

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_380 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 6] = *b"EXAMPL";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_381 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 6] = [1, 2, 3, 4, 5, 6];
        let mut p1: u8 = 3;

        <[u8; 6] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_382 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 6] = [1, 2, 3, 4, 5, 6];
        let p1: &u8 = &3;

        <[u8; 6] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_383 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 7] = [42, 55, 123, 0, 255, 64, 32];

        <[u8; 7] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_384 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let p0: &[u8; 7] = b"abcdefg";

        <&[u8; 7] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_385 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 7] = &[1, 2, 3, 4, 5, 6, 7];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_386 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 7] = &[1, 2, 3, 4, 5, 6, 7];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_387 {
    use super::*;
    use crate::InputIter;
    use crate::error::ErrorKind;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 7] = b"abcdefg";
        let mut p1 = |c| c == b'd';

        assert_eq!(p0.position(p1), Some(3));
    }
}#[cfg(test)]
mod tests_rug_388 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 7] = b"abcdefg";
        let mut p1: usize = 3;

        <&[u8; 7] as InputIter>::slice_index(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_389 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdefg";
        let mut p1: [u8; 7] = *b"abcdefg";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_390 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 7] = *b"EXAMPLE";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_391 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"exampledata";
        let mut p1: [u8; 7] = *b"example";

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_392 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example";
        let mut p1: [u8; 7] = *b"EXAMPLE";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_393 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];
        let mut p1: u8 = 4;

        <[u8; 7] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_394 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];
        let mut p1: &u8 = &3;

        <[u8; 7] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_395 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

        <[u8; 8] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_396 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 8] = &[1, 2, 3, 4, 5, 6, 7, 8];

        assert_eq!(p0.input_len(), 8);
    }
}#[cfg(test)]
mod tests_rug_397 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 8] = b"12345678";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_398 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 8] = &[1, 2, 3, 4, 5, 6, 7, 8];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_400 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 8] = &[1, 2, 3, 4, 5, 6, 7, 8];
        let mut p1: usize = 3;

        <&[u8; 8] as InputIter>::slice_index(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_401 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdefgh"; // Sample data for &'a [u8]
        let mut p1: [u8; 8] = *b"abcdefgh"; // Sample data for [u8; 8]

        <&[u8] as Compare<[u8; 8]>>::compare(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_403 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdefgh"; // Sample data for &'a [u8]
        let mut p1: [u8; 8] = *b"abcdefgh"; // Sample data for [u8; 8]

        <&[u8] as Compare<&[u8; 8]>>::compare(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_404 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 8] = *b"helloWor";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Incomplete);
    }
}#[cfg(test)]
mod tests_rug_405 {
    use super::*;
    use crate::FindToken;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
        let mut p1: u8 = 3;

        <[u8; 8] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_406 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
        let mut p1: &u8 = &3;

        <[u8; 8] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_407 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 9] = [1, 2, 3, 4, 5, 6, 7, 8, 9];

        <[u8; 9] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_408 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 9] = &[1, 2, 3, 4, 5, 6, 7, 8, 9];

        assert_eq!(p0.input_len(), 9);
    }
}#[cfg(test)]
mod tests_rug_409 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 9] = b"123456789";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_410 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 9] = b"123456789";

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_412 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 9] = &[1, 2, 3, 4, 5, 6, 7, 8, 9];
        let mut p1: usize = 3;

        <&[u8; 9] as InputIter>::slice_index(&p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_413 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"somebytes1"; // Sample data for &'a [u8]
        let mut p1: [u8; 9] = *b"somebytes"; // Sample data for [u8; 9]

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_414 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 9] = *b"helloWorl";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_415 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"somebytes1";
        let mut p1: [u8; 9] = *b"somebytes";

        <&[u8] as Compare<&[u8; 9]>>::compare(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_416 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 9] = *b"helloWorl";

        p0.compare_no_case(&p1);
    }
}#[cfg(test)]
mod tests_rug_417 {
    use super::*;
    use crate::FindToken;
    #[test]
    fn test_rug() {
        let mut p0: [u8; 9] = [1, 2, 3, 4, 5, 6, 7, 8, 9];
        let mut p1: u8 = 5;

        <[u8; 9] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_418 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 9] = [1, 2, 3, 4, 5, 6, 7, 8, 9];
        let p1: &u8 = &5;

        <[u8; 9] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_419 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

        <[u8; 10] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_420 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 10] = b"1234567890";

        assert_eq!(p0.input_len(), 10);
    }
}#[cfg(test)]
mod tests_rug_421 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 10] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_422 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 10] = &[42, 55, 69, 255, 0, 1, 3, 7, 11, 13];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_424 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 10] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let mut p1: usize = 3;

        <&[u8; 10] as InputIter>::slice_index(&p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_425 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"somebyte";
        let mut p1: [u8; 10] = *b"anotherbyt";

        <&[u8] as Compare<[u8; 10]>>::compare(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_426 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 10] = *b"HELLOWORLD";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_427 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"some bytes";
        let mut p1: [u8; 10] = [0x73, 0x6f, 0x6d, 0x65, 0x20, 0x62, 0x79, 0x74, 0x65, 0x73];

        <&[u8] as Compare<&[u8; 10]>>::compare(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_428 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 10] = *b"helloworld";

        p0.compare_no_case(&p1);
    }
}#[cfg(test)]
mod tests_rug_429 {
    use super::*;
    use crate::FindToken;
    use memchr;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 10] = [0x42, 0x65, 0x72, 0x74, 0x6c, 0x65, 0x79, 0x20, 0x4d, 0x6f];
        let mut p1: u8 = 0x65;

        assert!(<[u8; 10] as FindToken<u8>>::find_token(&p0, p1));
    }
}#[cfg(test)]
mod tests_rug_430 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let p1: &u8 = &5;

        <[u8; 10] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_431 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 11] = [42; 11];

        <[u8; 11] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_432 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 11] = b"hello world";

        assert_eq!(p0.input_len(), 11);
    }
}#[cfg(test)]
mod tests_rug_433 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 11] = b"hello_world";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_434 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 11] = b"hello_world";

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_436 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 11] = b"hello world";
        let mut p1: usize = 5;

        <&[u8; 11] as InputIter>::slice_index(&p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_437 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello_world";
        let mut p1: [u8; 11] = *b"hello_world";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_439 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello world";
        let mut p1: [u8; 11] = *b"hello world";

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_441 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 11] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let mut p1: u8 = 5;

        <[u8; 11] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_442 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 11] = [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x57, 0x6f, 0x72, 0x6c, 0x64];
        let mut p1: &u8 = &0x20;

        <[u8; 11] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_443 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 12] = [42; 12];

        <[u8; 12] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_444 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 12] = &[42, 55, 66, 77, 88, 99, 100, 111, 122, 133, 144, 155];

        assert_eq!(p0.input_len(), 12);
    }
}#[cfg(test)]
mod tests_rug_445 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 12] = b"hello world!";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_446 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 12] = &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_448 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 12] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let mut p1: usize = 5;

        let result = p0.slice_index(p1);
        assert_eq!(result, Ok(5));
    }
}#[cfg(test)]
mod tests_rug_449 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, world!";
        let mut p1: [u8; 12] = *b"Hello, world";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_451 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!";
        let mut p1: [u8; 12] = *b"Hello, World";

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_453 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let mut p1: u8 = 5;

        <[u8; 12] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_454 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 12] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let mut p1: &u8 = &5;

        <[u8; 12] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_455 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 13] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C];

        <[u8; 13] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_456 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 13] = b"Hello, World!";

        assert_eq!(p0.input_len(), 13);
    }
}#[cfg(test)]
mod tests_rug_457 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 13] = b"Hello, World!";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_458 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 13] = b"Hello, World!";

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_460 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 13] = b"Hello, World!";
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_461 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!";
        let mut p1: [u8; 13] = *b"Hello, World!";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_462 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!";
        let mut p1: [u8; 13] = *b"hello, world!";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_464 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!";
        let mut p1: [u8; 13] = *b"hello, world!";

        assert_eq!(p0.compare_no_case(&p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_465 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 13] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d];
        let mut p1: u8 = 0x05;

        <[u8; 13] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_466 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 13] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let mut p1: u8 = 5;

        <[u8; 13] as FindToken<&u8>>::find_token(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_467 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 14] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];

        assert_eq!(<[u8; 14] as InputLength>::input_len(&p0), 14);
    }
}#[cfg(test)]
mod tests_rug_468 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 14] = b"Hello, World!!";

        assert_eq!(p0.input_len(), 14);
    }
}#[cfg(test)]
mod tests_rug_470 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 14] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_471 {
    use super::*;
    use crate::InputIter;
    use crate::error::ErrorKind;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 14] = b"Hello, world!!";
        let mut p1 = |c: u8| c == b',' as u8;

        p0.position(p1);
    }
}#[cfg(test)]
mod tests_rug_472 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 14] = b"Hello, World!!";
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_473 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!!";
        let mut p1: [u8; 14] = *b"Hello, World!!";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_475 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"hello_world!";
        let mut p1: [u8; 14] = *b"hello_world!!!";

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_477 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 14] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e];
        let mut p1: u8 = 0x05;

        <[u8; 14] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_478 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 14] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E];
        let mut p1: &u8 = &0x05;

        <[u8; 14] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_479 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let p0: [u8; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];

        <[u8; 15] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_480 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 15] = &[42; 15];

        assert_eq!(p0.input_len(), 15);
    }
}#[cfg(test)]
mod tests_rug_483 {
    use super::*;
    use crate::InputIter;
    use std::boxed::Box;

    #[test]
    fn test_rug() {
        let p0: &[u8; 15] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let p1: Box<dyn Fn(u8) -> bool> = Box::new(|x| x == 5);

        assert_eq!(p0.position(p1), Some(5));
    }
}#[cfg(test)]
mod tests_rug_484 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 15] = b"Hello, world!!!";
        let mut p1: usize = 7;

        <&[u8; 15] as InputIter>::slice_index(&p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_485 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!"; // Sample data for &'a [u8]
        let mut p1: [u8; 15] = *b"Hello, World!!!"; // Sample data for [u8; 15]

        <&[u8] as Compare<[u8; 15]>>::compare(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_487 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!"; // Sample data for &'a [u8]
        let mut p1: [u8; 15] = *b"Hello, World!!!"; // Sample data for [u8; 15]

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_489 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut p1: u8 = 5;

        assert_eq!(<[u8; 15] as FindToken<u8>>::find_token(&p0, p1), true);

        let mut p1: u8 = 20;
        assert_eq!(<[u8; 15] as FindToken<u8>>::find_token(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_490 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        let mut p1: &u8 = &5;

        <[u8; 15] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_491 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 16] = [42; 16];

        <[u8; 16] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_492 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 16] = &[42u8; 16];

        assert_eq!(p0.input_len(), 16);
    }
}#[cfg(test)]
mod tests_rug_493 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 16] = &[42; 16];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_494 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 16] = &[42; 16];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_496 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 16] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_499 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example_data";
        let mut p1: [u8; 16] = *b"another_example_";

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_500 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!";
        let mut p1: [u8; 16] = *b"HELLO, WORLD!   ";

        p0.compare_no_case(&p1);
    }
}#[cfg(test)]
mod tests_rug_501 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut p1: u8 = 5;

        assert!(<[u8; 16] as FindToken<u8>>::find_token(&p0, p1));
        
        let mut p1: u8 = 20;
        assert!(!<[u8; 16] as FindToken<u8>>::find_token(&p0, p1));
    }
}#[cfg(test)]
mod tests_rug_502 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let mut p1: &u8 = &5;

        assert_eq!(<[u8; 16] as FindToken<&u8>>::find_token(&p0, p1), true);
    }
}#[cfg(test)]
mod tests_rug_503 {
    use super::*;
    use crate::traits::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 17] = [42; 17];

        assert_eq!(<[u8; 17] as InputLength>::input_len(&p0), 17);
    }
}#[cfg(test)]
mod tests_rug_504 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 17] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

        assert_eq!(p0.input_len(), 17);
    }
}#[cfg(test)]
mod tests_rug_505 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 17] = b"some_sample_data_";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_506 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 17] = &[42u8; 17];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_508 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 17] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_509 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"this_is_a_sample_";
        let mut p1: [u8; 17] = *b"this_is_a_sample_";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_511 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"some example byte slice";
        let mut p1: [u8; 17] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10];

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_512 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"example_data_here";
        let mut p1: [u8; 17] = *b"Example_Data_Here";

        p0.compare_no_case(&p1);
    }
}#[cfg(test)]
mod tests_rug_513 {
    use super::*;
    use crate::FindToken;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 17] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut p1: u8 = 5;

        assert_eq!(<[u8; 17] as FindToken<u8>>::find_token(&p0, p1), true);

        // Test case where the token is not present
        p1 = 20;
        assert_eq!(<[u8; 17] as FindToken<u8>>::find_token(&p0, p1), false);
    }
}#[cfg(test)]
mod tests_rug_514 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 17] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let mut p1: &u8 = &5;

        <[u8; 17] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_515 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 18] = [42; 18];

        <[u8; 18] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_516 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 18] = &[42; 18];

        assert_eq!(p0.input_len(), 18);
    }
}#[cfg(test)]
mod tests_rug_518 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 18] = &[42, 55, 69, 73, 88, 99, 101, 111, 123, 134, 145, 156, 167, 178, 189, 190, 200, 210];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_520 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 18] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17];
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_522 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 18] = *b"HELLOWORLDxxxxxxxx";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_525 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 18] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17];
        let mut p1: u8 = 5;

        assert_eq!(<[u8; 18] as FindToken<u8>>::find_token(&p0, p1), true);

        let mut p2: [u8; 18] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17];
        let mut p3: u8 = 20;

        assert_eq!(<[u8; 18] as FindToken<u8>>::find_token(&p2, p3), false);
    }
}#[cfg(test)]
mod tests_rug_526 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 18] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17];
        let mut p1: &u8 = &5;

        <[u8; 18] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_527 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 19] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19];

        let length = <[u8; 19] as InputLength>::input_len(&p0);
        assert_eq!(length, 19);
    }
}#[cfg(test)]
mod tests_rug_537 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 19] = [0x52, 0x75, 0x73, 0x74, 0x20, 0x69, 0x73, 0x20, 0x61, 0x20, 0x72, 0x75, 0x73, 0x74, 0x20, 0x74, 0x68, 0x69, 0x6e];
        let mut p1: u8 = 0x69; // 'i' in ASCII

        <[u8; 19] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_538 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 19] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18];
        let mut p1: &u8 = &5;

        <[u8; 19] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_539 {
    use super::*;
    use crate::traits::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 20] = [42; 20];

        assert_eq!(<[u8; 20] as InputLength>::input_len(&p0), 20);
    }
}#[cfg(test)]
mod tests_rug_540 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 20] = &[42u8; 20];

        assert_eq!(p0.input_len(), 20);
    }
}#[cfg(test)]
mod tests_rug_542 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 20] = &[42; 20];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_543 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 20] = b"some example data   "; // Sample data to initialize the byte array
        let mut p1 = char::is_whitespace as fn(char) -> bool; // Using the is_whitespace function from char

        assert_eq!(p0.position(|b| p1(b as char)), Some(17)); // Example assertion, adjust as necessary
    }
}#[cfg(test)]
mod tests_rug_544 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 20] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_545 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"some byte slice";
        let mut p1: [u8; 20] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13];

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_546 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let p0: &[u8] = b"HelloWorld";
        let p1: [u8; 20] = *b"HELLOWORLD\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_549 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 20] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
        let mut p1: u8 = 5;

        <[u8; 20] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_550 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 20] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];
        let mut p1: u8 = 5;

        <[u8; 20] as FindToken<&u8>>::find_token(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_551 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 21] = [42; 21];

        <[u8; 21] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_558 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorldThisIsATest";
        let mut p1: [u8; 21] = *b"HelloWorldThisIsATest";

        assert_eq!(p0.compare_no_case(p1), CompareResult::Ok);
    }
}#[cfg(test)]
mod tests_rug_561 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 21] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
        let mut p1: u8 = 10;

        assert!(<[u8; 21] as FindToken<u8>>::find_token(&p0, p1));
    }
}#[cfg(test)]
mod tests_rug_562 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 21] = [49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107];
        let mut p1: &u8 = &50;

        <[u8; 21] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_563 {
    use super::*;
    use crate::traits::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 22] = [42; 22];

        assert_eq!(<[u8; 22] as InputLength>::input_len(&p0), 22);
    }
}#[cfg(test)]
mod tests_rug_568 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 22] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22];
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_573 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 22] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21];
        let mut p1: u8 = 10;

        <[u8; 22] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_574 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 22] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22];
        let mut p1: &u8 = &3;

        <[u8; 22] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_575 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 23] = [42; 23];

        <[u8; 23] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_576 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 23] = &[49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51];

        p0.input_len();
    }
}#[cfg(test)]
mod tests_rug_585 {
    use super::*;
    use crate::FindToken;
    
    #[test]
    fn test_rug() {
        let mut p0: [u8; 23] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23];
        let mut p1: u8 = 5;

        <[u8; 23] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_586 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 23] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23];
        let mut p1: u8 = 5;

        <[u8; 23] as FindToken<&u8>>::find_token(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_587 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 24] = [0; 24];

        p0.input_len();
    }
}#[cfg(test)]
mod tests_rug_588 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 24] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];

        p0.input_len();
    }
}#[cfg(test)]
mod tests_rug_589 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 24] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_590 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 24] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_592 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 24] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_594 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"HelloWorld";
        let mut p1: [u8; 24] = *b"HELLOWORLDAAAAAAAAAAAAAA";

        assert_eq!(p0.compare_no_case(p1), CompareResult::Incomplete);
    }
}#[cfg(test)]
mod tests_rug_595 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"this is a sample byte slice";
        let mut p1: [u8; 24] = [0x74, 0x68, 0x69, 0x73, 0x20, 0x69, 0x73, 0x20, 0x61, 0x20, 0x73, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x20, 0x62, 0x79, 0x74, 0x65, 0x20, 0x73, 0x6c];

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_597 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 24] = [0x1a, 0x2b, 0x3c, 0x4d, 0x5e, 0x6f, 0x70, 0x81, 0x92, 0xa3, 0xb4, 0xc5, 0xd6, 0xe7, 0xf8, 0x09, 0x1a, 0x2b, 0x3c, 0x4d, 0x5e, 0x6f, 0x70, 0x81];
        let mut p1: u8 = 0x3c;

        <[u8; 24] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_598 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 24] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];
        let p1: &u8 = &5;

        <[u8; 24] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_599 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 25] = [42; 25];

        <[u8; 25] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_600 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 25] = &[49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53];

        p0.input_len();
    }
}#[cfg(test)]
mod tests_rug_602 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 25] = &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
            10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
            20, 21, 22, 23, 24
        ];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_604 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 25] = &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];
        let mut p1: usize = 5;

        p0.slice_index(p1);
    }
}#[cfg(test)]
mod tests_rug_609 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 25] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24];
        let mut p1: u8 = 5;

        <[u8; 25] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_610 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 25] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25];
        let mut p1: &u8 = &3;

        <[u8; 25] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_611 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 26] = *b"abcdefghijklmnopqrstuvwxyz";

        <[u8; 26] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_612 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 26] = b"abcdefghijklmnopqrstuvwxyz";

        assert_eq!(p0.input_len(), 26);
    }
}#[cfg(test)]
mod tests_rug_613 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 26] = b"abcdefghijklmnopqrstuvwxyz";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_614 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 26] = b"abcdefghijklmnopqrstuvwxyz";

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_616 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 26] = b"abcdefghijklmnopqrstuvwxyz";
        let mut p1: usize = 5;

        <&[u8; 26] as InputIter>::slice_index(&p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_617 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
        let mut p1: [u8; 26] = *b"abcdefghijklmnopqrstuvwxyz";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_618 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
        let mut p1: [u8; 26] = *b"ABCDEFGHIJKLMNOPQRSTUVWXYZ";

        p0.compare_no_case(p1);
    }
}#[cfg(test)]
mod tests_rug_619 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
        let mut p1: [u8; 26] = *b"abcdefghijklmnopqrstuvwxyz";

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_621 {
    use super::*;
    use crate::FindToken;
    use memchr;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 26] = *b"abcdefghijklmnopqrstuvwxyz";
        let mut p1: u8 = b'a';

        <[u8; 26] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_622 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 26] = [b'a', b'b', b'c', b'd', b'e', b'f', b'g', b'h', b'i', b'j', b'k', b'l', b'm', b'n', b'o', b'p', b'q', b'r', b's', b't', b'u', b'v', b'w', b'x', b'y', b'z'];
        let mut p1: u8 = b'a';

        <[u8; 26] as FindToken<&u8>>::find_token(&p0, &p1);
    }
}#[cfg(test)]
mod tests_rug_623 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 27] = [42; 27];

        <[u8; 27] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_629 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
        let mut p1: [u8; 27] = *b"abcdefghijklmnopqrstuvwxyz!";

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_633 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 27] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27];
        let mut p1: u8 = 10;

        <[u8; 27] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_634 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 27] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27];
        let p1: &u8 = &5;

        <[u8; 27] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_635 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 28] = [42; 28];

        <[u8; 28] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_636 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 28] = &[0u8; 28];

        p0.input_len();
    }
}#[cfg(test)]
mod tests_rug_637 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 28] = &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27
        ];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_638 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 28] = &[49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_640 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 28] = &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28];
        let mut p1: usize = 5;

        assert_eq!(p0.slice_index(p1), Ok(5));
    }
}#[cfg(test)]
mod tests_rug_645 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 28] = [97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 33, 64];
        let mut p1: u8 = 100;

        <[u8; 28] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_646 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 28] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28];
        let mut p1: &u8 = &5;

        <[u8; 28] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_647 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 29] = [42; 29];

        <[u8; 29] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_648 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 29] = b"abcdefghijklmnopqrstuvwxyz123";

        assert_eq!(p0.input_len(), 29);
    }
}#[cfg(test)]
mod tests_rug_649 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 29] = b"abcdefghijklmnopqrstuvwxyz123";

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_650 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 29] = b"abcdefghijklmnopqrstuvwxyz123";

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_651 {
    use super::*;
    use crate::InputIter;
    use core::str;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 29] = b"abcdefghijklmnopqrstuvwxyz123";
        let mut p1 = |c: u8| c == b'5';

        p0.position(p1);
    }
}#[cfg(test)]
mod tests_rug_652 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 29] = b"abcdefghijklmnopqrstuvwxyz123";
        let mut p1: usize = 5;

        <&[u8; 29] as InputIter>::slice_index(&p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_657 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 29] = [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
        ];
        let mut p1: u8 = 15;

        <[u8; 29] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_658 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 29] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29];
        let mut p1: &u8 = &5;

        <[u8; 29] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_659 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 30] = [42; 30];

        <[u8; 30] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_660 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 30] = &[0u8; 30];

        assert_eq!(p0.input_len(), 30);
    }
}#[cfg(test)]
mod tests_rug_661 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 30] = &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
            10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
            20, 21, 22, 23, 24, 25, 26, 27, 28, 29
        ];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_662 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 30] = &[49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_664 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 30] = &[0u8; 30];
        let mut p1: usize = 5;

        p0.slice_index(p1);
    }
}#[cfg(test)]
mod tests_rug_665 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"some byte slice";
        let mut p1: [u8; 30] = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
            21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
        ];

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_669 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 30] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29];
        let mut p1: u8 = 15;

        <[u8; 30] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_670 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 30] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30];
        let mut p1: &u8 = &5;

        <[u8; 30] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_671 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 31] = [42; 31];

        <[u8; 31] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_672 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 31] = &[42; 31];

        assert_eq!(p0.input_len(), 31);
    }
}#[cfg(test)]
mod tests_rug_673 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 31] = &[42; 31];

        p0.iter_indices();
    }
}#[cfg(test)]
mod tests_rug_674 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 31] = b"abcdefghijklmnopqrstuvwxyzabcde";

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_676 {
    use super::*;
    use crate::InputIter;
    #[test]
    fn test_rug() {
        let mut p0: &[u8; 31] = b"abcdefghijklmnopqrstuvwxyz12345";
        let mut p1: usize = 5;

        <&[u8; 31] as InputIter>::slice_index(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_681 {
    use super::*;
    use crate::FindToken;
    #[test]
    fn test_rug() {
        let mut p0: [u8; 31] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E];
        let mut p1: u8 = 0x0F;

        <[u8; 31] as FindToken<u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_682 {
    use super::*;
    use crate::traits::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 31] = [42; 31];
        let mut p1: &u8 = &5;

        <[u8; 31] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_683 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [42; 32];

        <[u8; 32] as InputLength>::input_len(&p0);
    }
}#[cfg(test)]
mod tests_rug_684 {
    use super::*;
    use crate::InputLength;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 32] = &[42; 32];

        p0.input_len();
    }
}#[cfg(test)]
mod tests_rug_686 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 32] = &[
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
            17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        ];

        p0.iter_elements();
    }
}#[cfg(test)]
mod tests_rug_688 {
    use super::*;
    use crate::InputIter;

    #[test]
    fn test_rug() {
        let mut p0: &[u8; 32] = &[42; 32];
        let mut p1: usize = 16;

        let result = p0.slice_index(p1);
        assert_eq!(result, Ok(16));
    }
}#[cfg(test)]
mod tests_rug_689 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"this is a sample byte slice";
        let mut p1: [u8; 32] = [42; 32]; // Example initialization with all elements set to 42

        p0.compare(p1);
    }
}#[cfg(test)]
mod tests_rug_691 {
    use super::*;
    use crate::Compare;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"this is a sample byte slice";
        let mut p1: [u8; 32] = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
            17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
        ];

        p0.compare(&p1);
    }
}#[cfg(test)]
mod tests_rug_693 {
    use super::*;
    use crate::FindToken;
    use memchr;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20];
        let mut p1: u8 = 0x05;

        assert!(<[u8; 32] as FindToken<u8>>::find_token(&p0, p1));
        
        let mut p1: u8 = 0xFF;
        assert!(!<[u8; 32] as FindToken<u8>>::find_token(&p0, p1));
    }
}#[cfg(test)]
mod tests_rug_694 {
    use super::*;
    use crate::FindToken;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 32] = [42; 32];
        let p1: &u8 = &5;

        <[u8; 32] as FindToken<&u8>>::find_token(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_695 {
    use super::*;
    use crate::traits::ExtendInto;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"sample";

        <[u8] as ExtendInto>::new_builder(p0);
    }
}#[cfg(test)]
mod tests_rug_696 {
    use super::*;
    use crate::traits::ExtendInto;
    
    #[test]
    fn test_rug() {
        let p0: &[u8] = b"hello"; // sample data for &[u8]
        let mut p1: std::vec::Vec<u8> = std::vec::Vec::<u8>::from([1, 2, 3, 4, 5]);

        <[u8] as ExtendInto>::extend_into(p0, &mut p1);

        assert_eq!(p1, vec![1, 2, 3, 4, 5, 104, 101, 108, 108, 111]);
    }
}#[cfg(test)]
mod tests_rug_697 {
    use super::*;
    use crate::traits::ExtendInto;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"sample data";

        p0.new_builder();
    }
}#[cfg(test)]
mod tests_rug_698 {
    use super::*;
    use crate::traits::ExtendInto;
    
    #[test]
    fn test_rug() {
        let p0: &[u8] = b"hello"; // sample data for &[u8]
        let mut p1: std::vec::Vec<u8> = std::vec::Vec::<u8>::from([1, 2, 3, 4, 5]); // create the local variable with type std::vec::Vec<u8>
        
        p0.extend_into(&mut p1);

        assert_eq!(p1, vec![1, 2, 3, 4, 5, 104, 101, 108, 108, 111]);
    }
}#[cfg(test)]
mod tests_rug_699 {
    use super::*;
    use crate::traits::ExtendInto;

    #[test]
    fn test_rug() {
        let mut p0: &str = "sample string";

        <str as ExtendInto>::new_builder(p0);
    }
}#[cfg(test)]
mod tests_rug_700 {
    use super::*;
    use crate::traits::ExtendInto;

    #[test]
    fn test_rug() {
        let p0: &str = "sample string";
        let mut p1: std::string::String = String::from("initial content");

        <str>::extend_into(p0, &mut p1);
    }
}#[cfg(test)]
mod tests_rug_701 {
    use super::*;
    use crate::traits::ExtendInto;

    #[test]
    fn test_rug() {
        let mut p0: &str = "sample string";

        p0.new_builder();
    }
}#[cfg(test)]
mod tests_rug_702 {
    use super::*;
    use crate::traits::ExtendInto;
    use std::string::String;

    #[test]
    fn test_rug() {
        let mut p0: &str = "sample";
        let mut p1: String = String::from("initial");

        p0.extend_into(&mut p1);

        assert_eq!(p1, "initialsample");
    }
}#[cfg(test)]
mod tests_rug_703 {
    use super::*;
    use crate::traits::ExtendInto;

    #[test]
    fn test_rug() {
        let mut p0: char = 'a';

        <char as ExtendInto>::new_builder(&p0);
    }
}#[cfg(test)]
mod tests_rug_704 {
    use super::*;
    use crate::traits::ExtendInto;
    
    #[test]
    fn test_rug() {
        let p0: char = 'a';
        let mut p1: std::string::String = String::from("hello");

        <char as ExtendInto>::extend_into(&p0, &mut p1);

        assert_eq!(p1, "helloa");
    }
}#[cfg(test)]
mod tests_rug_705 {
    use super::*;
    use crate::ToUsize;

    #[test]
    fn test_rug() {
        let p0: u8 = 42;

        <u8 as ToUsize>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_706 {
    use super::*;
    use crate::ToUsize;

    #[test]
    fn test_rug() {
        let mut p0: u16 = 42; // Sample data for initialization

        <u16 as ToUsize>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_707 {
    use super::*;
    use crate::traits::ToUsize;

    #[test]
    fn test_rug() {
        let mut p0: usize = 42;

        <usize as ToUsize>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_708 {
    use super::*;
    use crate::traits::ToUsize;

    #[test]
    fn test_rug() {
        let mut p0: u32 = 42;

        assert_eq!(<u32 as ToUsize>::to_usize(&p0), 42);
    }
}#[cfg(test)]
mod tests_rug_709 {
    use super::*;
    use crate::ToUsize;

    #[test]
    fn test_rug() {
        let mut p0: u64 = 1234567890;

        <u64 as ToUsize>::to_usize(&p0);
    }
}#[cfg(test)]
mod tests_rug_711 {
    use super::*;
    use crate::ErrorConvert;
    use crate::error::{self, ErrorKind};

    #[test]
    fn test_rug() {
        let mut p0: (&str, error::ErrorKind) = ("sample_input", ErrorKind::Fail);

        <(&str, error::ErrorKind) as ErrorConvert<((&str, usize), error::ErrorKind)>>::convert(p0);
    }
}#[cfg(test)]
mod tests_rug_713 {
    use super::*;
    use crate::ErrorConvert;
    use crate::error::{Error, ErrorKind};

    #[test]
    fn test_rug() {
        let mut p0: Error<&str> = Error::new("sample_input", ErrorKind::Complete);

        <Error<&str>>::convert(p0);
    }
}#[cfg(test)]
mod tests_rug_716 {
    use super::*;
    use crate::ErrorConvert;

    #[test]
    fn test_rug() {
        let mut p0: () = ();

        <() as ErrorConvert<()>>::convert(p0);
    }
}#[cfg(test)]
mod tests_rug_717 {
    use super::*;
    use crate::HexDisplay;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, World!";
        let mut p1: usize = 2;

        <[u8] as HexDisplay>::to_hex(p0, p1);
    }
}#[cfg(test)]
mod tests_rug_718 {
    use super::*;
    use crate::HexDisplay;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"Hello, world!";
        let mut p1: usize = 4;
        let mut p2: usize = 0;

        <[u8]>::to_hex_from(p0, p1, p2);
    }
}#[cfg(test)]
mod tests_rug_719 {
    use super::*;
    use crate::HexDisplay;

    #[test]
    fn test_rug() {
        let mut p0: &str = "Hello, world!";
        let mut p1: usize = 2;

        <str>::to_hex(&p0, p1);
    }
}#[cfg(test)]
mod tests_rug_720 {
    use super::*;
    use crate::HexDisplay;

    #[test]
    fn test_rug() {
        let mut p0: &str = "hello world";
        let mut p1: usize = 2;
        let mut p2: usize = 3;

        <str as HexDisplay>::to_hex_from(p0, p1, p2);
    }
}