//! Character specific parsers and combinators
//!
//! Functions recognizing specific characters

#[cfg(test)]
mod tests;

pub mod complete;
pub mod streaming;

/// Tests if byte is ASCII alphabetic: A-Z, a-z
///
/// # Example
///
/// ```
/// # use nom::character::is_alphabetic;
/// assert_eq!(is_alphabetic(b'9'), false);
/// assert_eq!(is_alphabetic(b'a'), true);
/// ```
#[inline]
pub fn is_alphabetic(chr: u8) -> bool {
  (chr >= 0x41 && chr <= 0x5A) || (chr >= 0x61 && chr <= 0x7A)
}

/// Tests if byte is ASCII digit: 0-9
///
/// # Example
///
/// ```
/// # use nom::character::is_digit;
/// assert_eq!(is_digit(b'a'), false);
/// assert_eq!(is_digit(b'9'), true);
/// ```
#[inline]
pub fn is_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x39
}

/// Tests if byte is ASCII hex digit: 0-9, A-F, a-f
///
/// # Example
///
/// ```
/// # use nom::character::is_hex_digit;
/// assert_eq!(is_hex_digit(b'a'), true);
/// assert_eq!(is_hex_digit(b'9'), true);
/// assert_eq!(is_hex_digit(b'A'), true);
/// assert_eq!(is_hex_digit(b'x'), false);
/// ```
#[inline]
pub fn is_hex_digit(chr: u8) -> bool {
  (chr >= 0x30 && chr <= 0x39) || (chr >= 0x41 && chr <= 0x46) || (chr >= 0x61 && chr <= 0x66)
}

/// Tests if byte is ASCII octal digit: 0-7
///
/// # Example
///
/// ```
/// # use nom::character::is_oct_digit;
/// assert_eq!(is_oct_digit(b'a'), false);
/// assert_eq!(is_oct_digit(b'9'), false);
/// assert_eq!(is_oct_digit(b'6'), true);
/// ```
#[inline]
pub fn is_oct_digit(chr: u8) -> bool {
  chr >= 0x30 && chr <= 0x37
}

/// Tests if byte is ASCII alphanumeric: A-Z, a-z, 0-9
///
/// # Example
///
/// ```
/// # use nom::character::is_alphanumeric;
/// assert_eq!(is_alphanumeric(b'-'), false);
/// assert_eq!(is_alphanumeric(b'a'), true);
/// assert_eq!(is_alphanumeric(b'9'), true);
/// assert_eq!(is_alphanumeric(b'A'), true);
/// ```
#[inline]
pub fn is_alphanumeric(chr: u8) -> bool {
  is_alphabetic(chr) || is_digit(chr)
}

/// Tests if byte is ASCII space or tab
///
/// # Example
///
/// ```
/// # use nom::character::is_space;
/// assert_eq!(is_space(b'\n'), false);
/// assert_eq!(is_space(b'\r'), false);
/// assert_eq!(is_space(b' '), true);
/// assert_eq!(is_space(b'\t'), true);
/// ```
#[inline]
pub fn is_space(chr: u8) -> bool {
  chr == b' ' || chr == b'\t'
}

/// Tests if byte is ASCII newline: \n
///
/// # Example
///
/// ```
/// # use nom::character::is_newline;
/// assert_eq!(is_newline(b'\n'), true);
/// assert_eq!(is_newline(b'\r'), false);
/// assert_eq!(is_newline(b' '), false);
/// assert_eq!(is_newline(b'\t'), false);
/// ```
#[inline]
pub fn is_newline(chr: u8) -> bool {
  chr == b'\n'
}
#[cfg(test)]
mod tests_rug_827 {
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'a';

        assert_eq!(crate::character::is_alphabetic(p0), true);

        p0 = b'9';
        assert_eq!(crate::character::is_alphabetic(p0), false);

        p0 = b'Z';
        assert_eq!(crate::character::is_alphabetic(p0), true);

        p0 = b'z';
        assert_eq!(crate::character::is_alphabetic(p0), true);

        p0 = b'@';
        assert_eq!(crate::character::is_alphabetic(p0), false);
    }
}#[cfg(test)]
mod tests_rug_828 {
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'9';

        assert_eq!(crate::character::is_digit(p0), true);

        p0 = b'a';
        assert_eq!(crate::character::is_digit(p0), false);
    }
}#[cfg(test)]
mod tests_rug_829 {
    use super::*;

    #[test]
    fn test_rug() {
        let mut p0: u8 = b'a';

        assert_eq!(crate::character::is_hex_digit(p0), true);

        p0 = b'9';
        assert_eq!(crate::character::is_hex_digit(p0), true);

        p0 = b'A';
        assert_eq!(crate::character::is_hex_digit(p0), true);

        p0 = b'x';
        assert_eq!(crate::character::is_hex_digit(p0), false);
    }
}#[cfg(test)]
mod tests_rug_830 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let p0: u8 = b'6';

        assert_eq!(crate::character::is_oct_digit(p0), true);
    }

    #[test]
    fn test_non_oct_digit_char_a() {
        let p0: u8 = b'a';

        assert_eq!(crate::character::is_oct_digit(p0), false);
    }

    #[test]
    fn test_non_oct_digit_char_9() {
        let p0: u8 = b'9';

        assert_eq!(crate::character::is_oct_digit(p0), false);
    }
}#[cfg(test)]
mod tests_rug_831 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let p0: u8 = b'-';

        assert_eq!(crate::character::is_alphanumeric(p0), false);

        let p1: u8 = b'a';
        assert_eq!(crate::character::is_alphanumeric(p1), true);

        let p2: u8 = b'9';
        assert_eq!(crate::character::is_alphanumeric(p2), true);

        let p3: u8 = b'A';
        assert_eq!(crate::character::is_alphanumeric(p3), true);
    }
}#[cfg(test)]
mod tests_rug_832 {
    use super::*;

    #[test]
    fn test_is_space() {
        let p0: u8 = b' ';

        assert_eq!(crate::character::is_space(p0), true);

        let p1: u8 = b'\t';
        assert_eq!(crate::character::is_space(p1), true);

        let p2: u8 = b'\n';
        assert_eq!(crate::character::is_space(p2), false);

        let p3: u8 = b'\r';
        assert_eq!(crate::character::is_space(p3), false);
    }
}#[cfg(test)]
mod tests_rug_833 {
    use super::*;
    
    #[test]
    fn test_rug() {
        let mut p0: u8 = b'\n';

        assert_eq!(crate::character::is_newline(p0), true);
        
        p0 = b'\r';
        assert_eq!(crate::character::is_newline(p0), false);
        
        p0 = b' ';
        assert_eq!(crate::character::is_newline(p0), false);
        
        p0 = b'\t';
        assert_eq!(crate::character::is_newline(p0), false);
    }
}