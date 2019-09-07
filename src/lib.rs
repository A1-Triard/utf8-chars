#![allow(non_shorthand_field_patterns)]
extern crate arrayvec;

use std::{fmt, slice};
use std::char::{self};
use std::io::{self, BufRead};
use arrayvec::{ArrayVec};

/// An iterator over the chars of an instance of `BufRead`.
///
/// This struct is generally created by calling `chars` on a `BufRead`.
#[derive(Debug)]
pub struct Chars<'a, T: BufRead + ?Sized>(&'a mut T);

/// A byte sequence, representing an invalid or incomplete UTF-8-encoded char.
#[derive(Debug)]
pub struct InvalidChar(ArrayVec<[u8; SEQUENCE_MAX_LENGTH as usize]>);
impl InvalidChar {
    pub fn as_bytes(&self) -> &[u8] { &self.0 }
    pub fn into_bytes(self) -> ArrayVec<[u8; SEQUENCE_MAX_LENGTH as usize]> { self.0 }
}
impl fmt::Display for InvalidChar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid UTF-8 byte sequence")?;
        for b in &self.0 {
            write!(f, " {:02X}", b)?;
        }
        Ok(())
    }
}

impl<'a, T: BufRead> Iterator for Chars<'a, T> {
    type Item = Result<char, (InvalidChar, Option<io::Error>)>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.read_char() {
            Ok(Some(c)) => Some(Ok(c)),
            Ok(None) => None,
            Err(e) => Some(Err(e))
        }
    }
}

const SEQUENCE_MAX_LENGTH: u8 = 4;
const LEAD_BYTE_MASK: [u8; SEQUENCE_MAX_LENGTH as usize] = [0x80, 0xE0, 0xF0, 0xF8];
const LEAD_BYTE_PATTERN: [u8; SEQUENCE_MAX_LENGTH as usize] = [0x00, 0xC0, 0xE0, 0xF0];
const TAIL_BYTE_MASK: u8 = 0xC0;
const TAIL_BYTE_PATTERN: u8 = 0x80;
const TAIL_BYTE_VALUE_BITS: u8 = 6;
const SEQUENCE_MIN_VALUE: [u32; SEQUENCE_MAX_LENGTH as usize] = [0, 0x80, 0x800, 0x10000];

fn to_utf8(item: u32, expected_tail_bytes_count: u8, actual_tail_bytes_count: u8) -> ArrayVec<[u8; SEQUENCE_MAX_LENGTH as usize]> {
    let mut res = ArrayVec::new();
    let lead_byte = LEAD_BYTE_PATTERN[expected_tail_bytes_count as usize] |
                        ((item >> (TAIL_BYTE_VALUE_BITS * expected_tail_bytes_count)) as u8) & !LEAD_BYTE_MASK[expected_tail_bytes_count as usize];
    res.push(lead_byte);
    for tail_byte_index in 0..actual_tail_bytes_count {
        res.push(TAIL_BYTE_PATTERN | ((item >> ((expected_tail_bytes_count - 1 - tail_byte_index) * TAIL_BYTE_VALUE_BITS)) as u8) & !TAIL_BYTE_MASK);
    }
    res
}

fn fill_buf_and_ignore_interrupts(reader: &mut impl BufRead) -> io::Result<&[u8]> {
    let (buf_ptr, buf_len) = loop {
        match reader.fill_buf() {
            Ok(buf) => break (buf.as_ptr(), buf.len()),
            Err(e) => {
                if e.kind() != io::ErrorKind::Interrupted {
                    return Err(e)
                }
            }
        }
    };
    Ok(unsafe { slice::from_raw_parts(buf_ptr, buf_len) })
}

/// Extends [`BufRead`] with methods for reading chars.
pub trait BufReadCharsExt : BufRead {
    /// Returns an iterator over the chars of this reader.
    ///
    /// The iterator returned from this function will yield instances of `Result<char, (InvalidChar, Option<io::Error>)>`.
    ///
    /// See `read_char` function for a description of possible `Err`s.
    fn chars(&mut self) -> Chars<Self> { Chars(self) }

    /// Reads a char from the underlying reader. Returns
    /// - `Ok(Some(char))` if a char is succesfully readed,
    /// - `Ok(None)` if the stream has reached EOF before lead byte was readed,
    /// - `Err((invalid_char, None))` with non-empty `invalid_char` if an invalid UTF-8 bytes sequence readed,
    /// - `Err((incomplete_char, Some(e))` with non-empty `incomplete_char` and `e.kind() == io::ErrorKind::UnexpectedEof` if EOF occuried after some bytes readed,
    /// - and `Err((readed_bytes, Some(io_error)))` if an I/O error with kind differs from `ErrorKind::Interrupted` occuried.
    ///
    /// If this function encounters an error of the kind `io::ErrorKind::Interrupted` then the error is ignored and the operation will continue.
    ///
    /// The `InvalidChar` can contain an empty byte sequence if an I/O error occurs when read a lead byte.
    fn read_char(&mut self) -> Result<Option<char>, (InvalidChar, Option<io::Error>)>;
}

impl<T: BufRead> BufReadCharsExt for T {
    fn read_char(&mut self) -> Result<Option<char>, (InvalidChar, Option<io::Error>)> {
        match fill_buf_and_ignore_interrupts(self) {
            Err(e) => return Err((InvalidChar(ArrayVec::new()), Some(e))),
            Ok(buf) => {
                if buf.is_empty() { return Ok(None); }
                let lead_byte = buf[0];
                self.consume(1);
                let tail_bytes_count = 'r: loop {
                    for i in 0..SEQUENCE_MAX_LENGTH {
                        if lead_byte & LEAD_BYTE_MASK[i as usize] == LEAD_BYTE_PATTERN[i as usize] { break 'r i; }
                    }
                    let mut bytes = ArrayVec::new();
                    bytes.push(lead_byte);
                    return Err((InvalidChar(bytes), None));
                };
                let mut item = ((lead_byte & !LEAD_BYTE_MASK[tail_bytes_count as usize]) as u32) << (TAIL_BYTE_VALUE_BITS * tail_bytes_count);
                for tail_byte_index in 0..tail_bytes_count {
                    match fill_buf_and_ignore_interrupts(self) {
                        Err(e) => return Err((InvalidChar(to_utf8(item, tail_bytes_count, tail_byte_index)), Some(e))),
                        Ok(buf) => {
                            if buf.is_empty() {
                                return Err((InvalidChar(to_utf8(item, tail_bytes_count, tail_byte_index)), Some(io::Error::new(io::ErrorKind::UnexpectedEof, "unexpected EOF"))));
                            }
                            if buf[0] & TAIL_BYTE_MASK != TAIL_BYTE_PATTERN {
                                return Err((InvalidChar(to_utf8(item, tail_bytes_count, tail_byte_index)), None));
                            }
                            item |= ((buf[0] & !TAIL_BYTE_MASK) as u32) << ((tail_bytes_count - 1 - tail_byte_index) * TAIL_BYTE_VALUE_BITS);
                            self.consume(1);
                        }
                    }
                }
                if item < SEQUENCE_MIN_VALUE[tail_bytes_count as usize] {
                    return Err((InvalidChar(to_utf8(item, tail_bytes_count, tail_bytes_count)), None));
                }
                match char::from_u32(item) {
                    None => Err((InvalidChar(to_utf8(item, tail_bytes_count, tail_bytes_count)), None)),
                    Some(item) => Ok(Some(item))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, BufReader};
    use std::vec::{Vec};
    use crate::{BufReadCharsExt};

    #[test]
    fn read_valid_unicode() {
        assert_eq!(vec!['A', 'B', 'c', 'd', ' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', '\0'],
                    BufReader::new("ABcd АБвгд U\0".as_bytes()).chars().map(|x| x.unwrap()).collect::<Vec<_>>());
    }

    #[test]
    fn read_valid_unicode_from_dyn_read() {
        let mut bytes: &mut dyn BufRead = &mut BufReader::new("ABcd АБвгд UV".as_bytes());
        assert_eq!(vec!['A', 'B', 'c', 'd', ' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', 'V'], bytes.chars().map(|x| x.unwrap()).collect::<Vec<_>>());
    }

    #[test]
    fn do_not_take_extra_bytes() {
        let mut bytes = BufReader::new("ABcd АБвгд UV".as_bytes());
        assert_eq!(vec!['A', 'B', 'c', 'd'], bytes.chars().take(4).map(|x| x.unwrap()).collect::<Vec<_>>());
        assert_eq!(vec![' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', 'V'], bytes.chars().map(|x| x.unwrap()).collect::<Vec<_>>());
    }

    #[test]
    fn read_value_out_of_range() {
        let mut bytes = BufReader::new(&[ 0xF5, 0x8F, 0xBF, 0xBF ][..]);
        let res = bytes.chars().collect::<Vec<_>>();
        assert_eq!(1, res.len());
        let err = res[0].as_ref().err().unwrap();
        assert_eq!(&[0xF5, 0x8F, 0xBF, 0xBF][..], err.0.as_bytes());
    }

    #[test]
    fn read_surrogate() {
        let mut bytes = BufReader::new(&[ 0xED, 0xA0, 0x80 ][..]);
        let res = bytes.chars().collect::<Vec<_>>();
        assert_eq!(1, res.len());
        let err = res[0].as_ref().err().unwrap();
        assert_eq!(&[0xED, 0xA0, 0x80][..], err.0.as_bytes());
    }

    #[test]
    fn read_invalid_sequences() {
        let mut bytes = BufReader::new(&[ 0x81, 0x82, 0xC1, 0x07, 0xC1, 0x87, 0xC2, 0xC2, 0x82, 0xF7, 0x88, 0x89, 0x07 ][..]);
        let res = bytes.chars().collect::<Vec<_>>();
        assert_eq!(9, res.len());
        assert_eq!(&[0x81][..], res[0].as_ref().err().unwrap().0.as_bytes());
        assert_eq!(&[0x82][..], res[1].as_ref().err().unwrap().0.as_bytes());
        assert_eq!(&[0xC1][..], res[2].as_ref().err().unwrap().0.as_bytes());
        assert_eq!('\x07', *res[3].as_ref().unwrap());
        assert_eq!(&[0xC1, 0x87][..], res[4].as_ref().err().unwrap().0.as_bytes());
        assert_eq!(&[0xC2][..], res[5].as_ref().err().unwrap().0.as_bytes());
        assert_eq!('\u{82}', *res[6].as_ref().unwrap());
        assert_eq!(&[0xF7, 0x88, 0x89][..], res[7].as_ref().err().unwrap().0.as_bytes());
        assert_eq!('\x07', *res[8].as_ref().unwrap());
    }
}
