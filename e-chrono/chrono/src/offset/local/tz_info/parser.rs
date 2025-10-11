use std::io::{self, ErrorKind};
use std::iter;
use std::num::ParseIntError;
use std::str::{self, FromStr};

use super::rule::TransitionRule;
use super::timezone::{LeapSecond, LocalTimeType, TimeZone, Transition};
use super::Error;

pub(super) fn parse(bytes: &[u8]) -> Result<TimeZone, Error> {
    let mut cursor = Cursor::new(bytes);
    let state = State::new(&mut cursor, true)?;
    let (state, footer) = match state.header.version {
        Version::V1 => match cursor.is_empty() {
            true => (state, None),
            false => {
                return Err(Error::InvalidTzFile("remaining data after end of TZif v1 data block"))
            }
        },
        Version::V2 | Version::V3 => {
            let state = State::new(&mut cursor, false)?;
            (state, Some(cursor.remaining()))
        }
    };

    let mut transitions = Vec::with_capacity(state.header.transition_count);
    for (arr_time, &local_time_type_index) in
        state.transition_times.chunks_exact(state.time_size).zip(state.transition_types)
    {
        let unix_leap_time =
            state.parse_time(&arr_time[0..state.time_size], state.header.version)?;
        let local_time_type_index = local_time_type_index as usize;
        transitions.push(Transition::new(unix_leap_time, local_time_type_index));
    }

    let mut local_time_types = Vec::with_capacity(state.header.type_count);
    for arr in state.local_time_types.chunks_exact(6) {
        let ut_offset = read_be_i32(&arr[..4])?;

        let is_dst = match arr[4] {
            0 => false,
            1 => true,
            _ => return Err(Error::InvalidTzFile("invalid DST indicator")),
        };

        let char_index = arr[5] as usize;
        if char_index >= state.header.char_count {
            return Err(Error::InvalidTzFile("invalid time zone name char index"));
        }

        let position = match state.names[char_index..].iter().position(|&c| c == b'\0') {
            Some(position) => position,
            None => return Err(Error::InvalidTzFile("invalid time zone name char index")),
        };

        let name = &state.names[char_index..char_index + position];
        let name = if !name.is_empty() { Some(name) } else { None };
        local_time_types.push(LocalTimeType::new(ut_offset, is_dst, name)?);
    }

    let mut leap_seconds = Vec::with_capacity(state.header.leap_count);
    for arr in state.leap_seconds.chunks_exact(state.time_size + 4) {
        let unix_leap_time = state.parse_time(&arr[0..state.time_size], state.header.version)?;
        let correction = read_be_i32(&arr[state.time_size..state.time_size + 4])?;
        leap_seconds.push(LeapSecond::new(unix_leap_time, correction));
    }

    let std_walls_iter = state.std_walls.iter().copied().chain(iter::repeat(0));
    let ut_locals_iter = state.ut_locals.iter().copied().chain(iter::repeat(0));
    if std_walls_iter.zip(ut_locals_iter).take(state.header.type_count).any(|pair| pair == (0, 1)) {
        return Err(Error::InvalidTzFile(
            "invalid couple of standard/wall and UT/local indicators",
        ));
    }

    let extra_rule = match footer {
        Some(footer) => {
            let footer = str::from_utf8(footer)?;
            if !(footer.starts_with('\n') && footer.ends_with('\n')) {
                return Err(Error::InvalidTzFile("invalid footer"));
            }

            let tz_string = footer.trim_matches(|c: char| c.is_ascii_whitespace());
            if tz_string.starts_with(':') || tz_string.contains('\0') {
                return Err(Error::InvalidTzFile("invalid footer"));
            }

            match tz_string.is_empty() {
                true => None,
                false => Some(TransitionRule::from_tz_string(
                    tz_string.as_bytes(),
                    state.header.version == Version::V3,
                )?),
            }
        }
        None => None,
    };

    TimeZone::new(transitions, local_time_types, leap_seconds, extra_rule)
}

/// TZif data blocks
struct State<'a> {
    header: Header,
    /// Time size in bytes
    time_size: usize,
    /// Transition times data block
    transition_times: &'a [u8],
    /// Transition types data block
    transition_types: &'a [u8],
    /// Local time types data block
    local_time_types: &'a [u8],
    /// Time zone names data block
    names: &'a [u8],
    /// Leap seconds data block
    leap_seconds: &'a [u8],
    /// UT/local indicators data block
    std_walls: &'a [u8],
    /// Standard/wall indicators data block
    ut_locals: &'a [u8],
}

impl<'a> State<'a> {
    /// Read TZif data blocks
    fn new(cursor: &mut Cursor<'a>, first: bool) -> Result<Self, Error> {
        let header = Header::new(cursor)?;
        let time_size = match first {
            true => 4, // We always parse V1 first
            false => 8,
        };

        Ok(Self {
            time_size,
            transition_times: cursor.read_exact(header.transition_count * time_size)?,
            transition_types: cursor.read_exact(header.transition_count)?,
            local_time_types: cursor.read_exact(header.type_count * 6)?,
            names: cursor.read_exact(header.char_count)?,
            leap_seconds: cursor.read_exact(header.leap_count * (time_size + 4))?,
            std_walls: cursor.read_exact(header.std_wall_count)?,
            ut_locals: cursor.read_exact(header.ut_local_count)?,
            header,
        })
    }

    /// Parse time values
    fn parse_time(&self, arr: &[u8], version: Version) -> Result<i64, Error> {
        match version {
            Version::V1 => Ok(read_be_i32(&arr[..4])?.into()),
            Version::V2 | Version::V3 => read_be_i64(arr),
        }
    }
}

/// TZif header
#[derive(Debug)]
struct Header {
    /// TZif version
    version: Version,
    /// Number of UT/local indicators
    ut_local_count: usize,
    /// Number of standard/wall indicators
    std_wall_count: usize,
    /// Number of leap-second records
    leap_count: usize,
    /// Number of transition times
    transition_count: usize,
    /// Number of local time type records
    type_count: usize,
    /// Number of time zone names bytes
    char_count: usize,
}

impl Header {
    fn new(cursor: &mut Cursor) -> Result<Self, Error> {
        let magic = cursor.read_exact(4)?;
        if magic != *b"TZif" {
            return Err(Error::InvalidTzFile("invalid magic number"));
        }

        let version = match cursor.read_exact(1)? {
            [0x00] => Version::V1,
            [0x32] => Version::V2,
            [0x33] => Version::V3,
            _ => return Err(Error::UnsupportedTzFile("unsupported TZif version")),
        };

        cursor.read_exact(15)?;
        let ut_local_count = cursor.read_be_u32()?;
        let std_wall_count = cursor.read_be_u32()?;
        let leap_count = cursor.read_be_u32()?;
        let transition_count = cursor.read_be_u32()?;
        let type_count = cursor.read_be_u32()?;
        let char_count = cursor.read_be_u32()?;

        if !(type_count != 0
            && char_count != 0
            && (ut_local_count == 0 || ut_local_count == type_count)
            && (std_wall_count == 0 || std_wall_count == type_count))
        {
            return Err(Error::InvalidTzFile("invalid header"));
        }

        Ok(Self {
            version,
            ut_local_count: ut_local_count as usize,
            std_wall_count: std_wall_count as usize,
            leap_count: leap_count as usize,
            transition_count: transition_count as usize,
            type_count: type_count as usize,
            char_count: char_count as usize,
        })
    }
}

/// A `Cursor` contains a slice of a buffer and a read count.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Cursor<'a> {
    /// Slice representing the remaining data to be read
    remaining: &'a [u8],
    /// Number of already read bytes
    read_count: usize,
}

impl<'a> Cursor<'a> {
    /// Construct a new `Cursor` from remaining data
    pub(crate) const fn new(remaining: &'a [u8]) -> Self {
        Self { remaining, read_count: 0 }
    }

    pub(crate) fn peek(&self) -> Option<&u8> {
        self.remaining().first()
    }

    /// Returns remaining data
    pub(crate) const fn remaining(&self) -> &'a [u8] {
        self.remaining
    }

    /// Returns `true` if data is remaining
    pub(crate) const fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }

    pub(crate) fn read_be_u32(&mut self) -> Result<u32, Error> {
        let mut buf = [0; 4];
        buf.copy_from_slice(self.read_exact(4)?);
        Ok(u32::from_be_bytes(buf))
    }

    /// Read exactly `count` bytes, reducing remaining data and incrementing read count
    pub(crate) fn read_exact(&mut self, count: usize) -> Result<&'a [u8], io::Error> {
        match (self.remaining.get(..count), self.remaining.get(count..)) {
            (Some(result), Some(remaining)) => {
                self.remaining = remaining;
                self.read_count += count;
                Ok(result)
            }
            _ => Err(io::Error::from(ErrorKind::UnexpectedEof)),
        }
    }

    /// Read bytes and compare them to the provided tag
    pub(crate) fn read_tag(&mut self, tag: &[u8]) -> Result<(), io::Error> {
        if self.read_exact(tag.len())? == tag {
            Ok(())
        } else {
            Err(io::Error::from(ErrorKind::InvalidData))
        }
    }

    /// Read bytes if the remaining data is prefixed by the provided tag
    pub(crate) fn read_optional_tag(&mut self, tag: &[u8]) -> Result<bool, io::Error> {
        if self.remaining.starts_with(tag) {
            self.read_exact(tag.len())?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Read bytes as long as the provided predicate is true
    pub(crate) fn read_while<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], io::Error> {
        match self.remaining.iter().position(|x| !f(x)) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
        }
    }

    // Parse an integer out of the ASCII digits
    pub(crate) fn read_int<T: FromStr<Err = ParseIntError>>(&mut self) -> Result<T, Error> {
        let bytes = self.read_while(u8::is_ascii_digit)?;
        Ok(str::from_utf8(bytes)?.parse()?)
    }

    /// Read bytes until the provided predicate is true
    pub(crate) fn read_until<F: Fn(&u8) -> bool>(&mut self, f: F) -> Result<&'a [u8], io::Error> {
        match self.remaining.iter().position(f) {
            None => self.read_exact(self.remaining.len()),
            Some(position) => self.read_exact(position),
        }
    }
}

pub(crate) fn read_be_i32(bytes: &[u8]) -> Result<i32, Error> {
    if bytes.len() != 4 {
        return Err(Error::InvalidSlice("too short for i32"));
    }

    let mut buf = [0; 4];
    buf.copy_from_slice(bytes);
    Ok(i32::from_be_bytes(buf))
}

pub(crate) fn read_be_i64(bytes: &[u8]) -> Result<i64, Error> {
    if bytes.len() != 8 {
        return Err(Error::InvalidSlice("too short for i64"));
    }

    let mut buf = [0; 8];
    buf.copy_from_slice(bytes);
    Ok(i64::from_be_bytes(buf))
}

/// TZif version
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Version {
    /// Version 1
    V1,
    /// Version 2
    V2,
    /// Version 3
    V3,
}
#[cfg(test)]
mod tests_rug_389 {
    use super::*;
    use crate::offset::local::tz_info::parser::parse;
    use std::io::Cursor;

    #[test]
    fn test_rug() {
        let p0: &[u8] = b"TZif2\0\0\0\0\0\0\0\x1c\0\0\0\0\0\0\0\x03\0\0\0\0\0\0\0\x00\0\0\0\0\0\0\x00\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0UTC\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0";

        parse(p0).unwrap();
    }
}#[cfg(test)]
mod tests_rug_391 {
    use super::*;
    use crate::offset::local::tz_info::parser::read_be_i64;
    use std::num::IntErrorKind;

    #[test]
    fn test_rug() {
        let p0: &[u8] = &[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0];

        match read_be_i64(p0) {
            Ok(value) => assert_eq!(value, 0x123456789ABCDEF0i64),
            Err(_) => panic!("Test failed with an unexpected error"),
        }
    }

    #[test]
    fn test_invalid_length() {
        let p0: &[u8] = &[0x12, 0x34, 0x56, 0x78];

        match read_be_i64(p0) {
            Ok(_) => panic!("Test should have failed with an error"),
            Err(e) => assert_eq!(e.to_string(), "invalid slice: too short for i64"),
        }
    }
}#[cfg(test)]
mod tests_rug_392 {
    use super::*;
    use crate::offset::local::tz_info::parser::{Cursor, State};

    #[test]
    fn test_rug() {
        let data = b"sample data";
        let mut p0: Cursor<'_> = Cursor::new(data);
        let p1: bool = true;

        <State<'_>>::new(&mut p0, p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_393 {
    use super::*;
    use crate::offset::local::tz_info::parser::{State, Version};
    use crate::offset::local::tz_info::parser::read_be_i32;
    use crate::offset::local::tz_info::parser::read_be_i64;

    #[test]
    fn test_parse_time() {
        let mut state: State<'_> = unsafe { std::mem::zeroed() };
        let data_v1: &[u8] = b"\x00\x00\x00\x01"; // Example data for Version::V1
        let data_v2: &[u8] = b"\x00\x00\x00\x00\x00\x00\x00\x01"; // Example data for Version::V2 or V3
        let version_v1: Version = Version::V1;
        let version_v2: Version = Version::V2;

        assert_eq!(state.parse_time(data_v1, version_v1).unwrap(), 1);
        assert_eq!(state.parse_time(data_v2, version_v2).unwrap(), 1);
    }
}#[cfg(test)]
mod tests_rug_394 {
    use super::*;
    use crate::offset::local::tz_info::parser::{Cursor, Header, Error};

    #[test]
    fn test_rug() {
        let mut p0 = Cursor::new(b"sample data");

        assert!(<Header>::new(&mut p0).is_err());

        let valid_data: &[u8] = b"TZif\x00\
                                  \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
                                  \x01\x00\x00\x00\
                                  \x01\x00\x00\x00\
                                  \x00\x00\x00\x00\
                                  \x02\x00\x00\x00\
                                  \x03";
        let mut valid_cursor = Cursor::new(valid_data);

        assert!(<Header>::new(&mut valid_cursor).is_ok());
    }
}#[cfg(test)]
mod tests_rug_395 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;

    #[test]
    fn test_rug() {
        let mut p0: &[u8] = b"sample_data";

        Cursor::new(p0);
    }
}#[cfg(test)]
mod tests_rug_396 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;

    #[test]
    fn test_rug() {
        let data = b"sample data";
        let mut p0: Cursor<'_> = Cursor::new(data);

        assert_eq!(p0.peek(), Some(&b's'));
    }
}#[cfg(test)]
mod tests_rug_397 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;

    #[test]
    fn test_remaining() {
        let data = b"sample data";
        let p0: Cursor<'_> = Cursor::new(data);

        assert_eq!(p0.remaining(), data);
    }
}#[cfg(test)]
mod tests_rug_398 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;

    #[test]
    fn test_is_empty() {
        let data = b"sample data";
        let mut p0: Cursor<'_> = Cursor::new(data);

        assert!(!p0.is_empty());

        // Test with an empty slice
        let empty_data = b"";
        let mut p1: Cursor<'_> = Cursor::new(empty_data);

        assert!(p1.is_empty());
    }
}#[cfg(test)]
mod tests_rug_399 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;

    #[test]
    fn test_read_be_u32() {
        let data = b"\x01\x02\x03\x04"; // Sample data that represents a big-endian u32 value 0x01020304
        let mut p0 = Cursor::new(data);

        match p0.read_be_u32() {
            Ok(value) => assert_eq!(value, 0x01020304),
            Err(e) => panic!("Failed to read u32: {}", e),
        }
    }
}#[cfg(test)]
mod tests_rug_400 {
    use crate::offset::local::tz_info::parser::Cursor;
    
    #[test]
    fn test_rug() {
        let data = b"sample data";
        let mut p0 = Cursor::new(data);
        let p1: usize = 5;

        p0.read_exact(p1).unwrap();
    }
}#[cfg(test)]
mod tests_rug_401 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;
    use std::io;

    #[test]
    fn test_read_tag() {
        let data = b"sample data";
        let mut p0 = Cursor::new(data);
        let p1: &[u8] = b"samp";

        assert!(p0.read_tag(p1).is_ok());

        let p2: &[u8] = b"invalid";
        assert!(p0.read_tag(p2).is_err());
    }
}#[cfg(test)]
mod tests_rug_402 {
    use crate::offset::local::tz_info::parser::Cursor;
    use std::io;

    #[test]
    fn test_read_optional_tag() {
        let data = b"sample data";
        let mut p0: Cursor<'_> = Cursor::new(data);
        let p1: &[u8] = b"sample";

        assert_eq!(p0.read_optional_tag(p1).unwrap(), true);

        // Test with a tag that is not present
        let p2: &[u8] = b"missing";
        assert_eq!(p0.read_optional_tag(p2).unwrap(), false);
    }
}#[cfg(test)]
mod tests_rug_403 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;

    #[test]
    fn test_rug() {
        let data = b"sample data";
        let mut cursor = Cursor::new(data);
        let predicate: fn(&u8) -> bool = |&x| x != b' ';
        
        cursor.read_while(predicate).unwrap();
    }
}#[cfg(test)]
mod tests_rug_404 {
    use super::*;
    use crate::offset::local::tz_info::parser::Cursor;

    #[test]
    fn test_rug() {
        let data = b"12345";
        let mut p0: Cursor<'_> = Cursor::new(data);

        assert_eq!(p0.read_int::<i32>().unwrap(), 12345);
    }
}