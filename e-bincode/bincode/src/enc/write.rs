//! This module contains writer-based structs and traits.
//!
//! Because `std::io::Write` is only limited to `std` and not `core`, we provide our own [Writer].

use crate::error::EncodeError;

/// Trait that indicates that a struct can be used as a destination to encode data too. This is used by [Encode]
///
/// [Encode]: ../trait.Encode.html
pub trait Writer {
    /// Write `bytes` to the underlying writer. Exactly `bytes.len()` bytes must be written, or else an error should be returned.
    fn write(&mut self, bytes: &[u8]) -> Result<(), EncodeError>;
}

impl<T: Writer> Writer for &mut T {
    #[inline]
    fn write(&mut self, bytes: &[u8]) -> Result<(), EncodeError> {
        (**self).write(bytes)
    }
}

/// A helper struct that implements `Writer` for a `&[u8]` slice.
///
/// ```
/// use bincode::enc::write::{Writer, SliceWriter};
///
/// let destination = &mut [0u8; 100];
/// let mut writer = SliceWriter::new(destination);
/// writer.write(&[1, 2, 3, 4, 5]).unwrap();
///
/// assert_eq!(writer.bytes_written(), 5);
/// assert_eq!(destination[0..6], [1, 2, 3, 4, 5, 0]);
/// ```
pub struct SliceWriter<'storage> {
    slice: &'storage mut [u8],
    original_length: usize,
}

impl<'storage> SliceWriter<'storage> {
    /// Create a new instance of `SliceWriter` with the given byte array.
    pub fn new(bytes: &'storage mut [u8]) -> SliceWriter<'storage> {
        let original = bytes.len();
        SliceWriter {
            slice: bytes,
            original_length: original,
        }
    }

    /// Return the amount of bytes written so far.
    pub fn bytes_written(&self) -> usize {
        self.original_length - self.slice.len()
    }
}

impl<'storage> Writer for SliceWriter<'storage> {
    #[inline(always)]
    fn write(&mut self, bytes: &[u8]) -> Result<(), EncodeError> {
        if bytes.len() > self.slice.len() {
            return Err(EncodeError::UnexpectedEnd);
        }
        let (a, b) = core::mem::take(&mut self.slice).split_at_mut(bytes.len());
        a.copy_from_slice(bytes);
        self.slice = b;

        Ok(())
    }
}

/// A writer that counts how many bytes were written. This is useful for e.g. pre-allocating buffers bfeore writing to them.
#[derive(Default)]
pub struct SizeWriter {
    /// the amount of bytes that were written so far
    pub bytes_written: usize,
}
impl Writer for SizeWriter {
    #[inline(always)]
    fn write(&mut self, bytes: &[u8]) -> Result<(), EncodeError> {
        self.bytes_written += bytes.len();

        Ok(())
    }
}
#[cfg(test)]
mod tests_rug_303 {
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: [u8; 4] = [0, 1, 2, 3];

        crate::enc::write::SliceWriter::new(&mut p0);
    }
}#[cfg(test)]
mod tests_rug_304 {
    use crate::enc::write::SliceWriter;

    #[test]
    fn test_rug() {
        let mut buffer = [0u8; 1024]; // Sample buffer to write into
        let p0: SliceWriter<'_> = SliceWriter::new(&mut buffer);

        assert_eq!(p0.bytes_written(), 0); // Initial check, no bytes written yet
    }
}#[cfg(test)]
mod tests_rug_305 {
    use super::*;
    use crate::enc::write::Writer;
    use crate::enc::write::SliceWriter;

    #[test]
    fn test_rug() {
        let mut buffer = [0u8; 1024]; // Sample buffer to write into
        let mut p0 = SliceWriter::new(&mut buffer);
        let p1: &[u8] = b"sample data"; // Sample byte slice

        <SliceWriter<'_>>::write(&mut p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_306 {
    use super::*;
    use crate::enc::write::{Writer, SizeWriter};

    #[test]
    fn test_rug() {
        let mut p0 = SizeWriter::default();
        let mut p1: &[u8] = b"sample data";

        <SizeWriter as Writer>::write(&mut p0, p1).unwrap();

        assert_eq!(p0.bytes_written, 11);
    }
}