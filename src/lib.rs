#![allow(non_shorthand_field_patterns)]
#![cfg_attr(test, feature(result_map_or_else))]
#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
extern crate arrayvec;

use std::{fmt, slice};
use std::char::{self};
use std::error::{Error};
use std::io::{self, BufRead};
use arrayvec::{ArrayVec};

/// A structure, containing readed bytes, and an [`io::Error`](https://doc.rust-lang.org/std/io/struct.Error.html).
/// The `io::Error` is an actual I/O error if some occuried,
/// or a synthetic error with either the [`UnexpectedEof`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html#variant.UnexpectedEof)
/// kind if a multi-byte char was unexpectedly terminated,
/// either the [`InvalidData`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html#variant.InvalidData)
/// kind if no actual I/O error occuried, but readed byte sequence was not recognised as a valid UTF-8.  
#[derive(Debug)]
pub struct ReadCharError {
    bytes: ArrayVec<[u8; SEQUENCE_MAX_LENGTH as usize]>,
    io_error: io::Error,
}

impl ReadCharError {
    /// A byte sequence, representing an invalid or incomplete UTF-8-encoded char.
    pub fn as_bytes(&self) -> &[u8] { &self.bytes }
    /// Returns a reference to the I/O error.
    pub fn as_io_error(&self) -> &io::Error { &self.io_error }
    /// Consumes the `ReadCharError`, returning the I/O error.
    pub fn into_io_error(self) -> io::Error { self.io_error }
}

impl Error for ReadCharError {
    fn source(&self) -> Option<&(dyn Error + 'static)> { Some(&self.io_error) }
}

impl fmt::Display for ReadCharError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid UTF-8 byte sequence")?;
        for b in self.as_bytes() {
            write!(f, " {:02X}", b)?;
        }
        write!(f, " readed")?;
        match self.as_io_error().kind() {
            io::ErrorKind::InvalidData => { },
            io::ErrorKind::UnexpectedEof => { write!(f, " (unexpected EOF)")?; }
            _ => { write!(f, " ({})", self.as_io_error())?; }
        }
        Ok(())
    }
}

/// An iterator over the chars of an instance of [`BufRead`](std::io::BufRead).
///
/// This struct is generally created by calling [`chars`](trait.BufReadCharsExt.html#method.chars)
/// on a [`BufRead`](https://doc.rust-lang.org/std/io/trait.BufRead.html).
#[derive(Debug)]
pub struct Chars<'a, T: BufRead + ?Sized>(&'a mut T);

impl<'a, T: BufRead + ?Sized> Iterator for Chars<'a, T> {
    type Item = Result<char, ReadCharError>;

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
    let lead_byte = LEAD_BYTE_PATTERN[expected_tail_bytes_count as usize] | ((item >> (TAIL_BYTE_VALUE_BITS * expected_tail_bytes_count)) as u8);
    res.push(lead_byte);
    for tail_byte_index in 0..actual_tail_bytes_count {
        res.push(TAIL_BYTE_PATTERN | ((item >> ((expected_tail_bytes_count - 1 - tail_byte_index) * TAIL_BYTE_VALUE_BITS)) as u8) & !TAIL_BYTE_MASK);
    }
    res
}

fn fill_buf_and_ignore_interrupts(reader: &mut (impl BufRead + ?Sized)) -> io::Result<&[u8]> {
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
    /// The iterator returned from this function will yield instances of [`Result`](https://doc.rust-lang.org/core/result/enum.Result.html)`<char, ReadCharError>`.
    fn chars(&mut self) -> Chars<Self> { Chars(self) }

    /// Reads a char from the underlying reader.
    ///
    /// Returns
    /// - `Ok(Some(char))` if a char has succesfully readed,
    /// - `Ok(None)` if the stream has reached EOF before any byte was readed,
    /// - `Err(err)` if an I/O error occuried, or readed byte sequence was not recognised as a valid UTF-8.
    ///
    /// If this function encounters an error of the kind `io::ErrorKind::Interrupted` then the error is ignored and the operation will continue.
    fn read_char(&mut self) -> Result<Option<char>, ReadCharError> {
        match fill_buf_and_ignore_interrupts(self) {
            Err(e) => return Err(ReadCharError { bytes: ArrayVec::new(), io_error: e }),
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
                    return Err(ReadCharError { bytes: bytes, io_error: io::Error::from(io::ErrorKind::InvalidData) });
                };
                let mut item = ((lead_byte & !LEAD_BYTE_MASK[tail_bytes_count as usize]) as u32) << (TAIL_BYTE_VALUE_BITS * tail_bytes_count);
                for tail_byte_index in 0..tail_bytes_count {
                    match fill_buf_and_ignore_interrupts(self) {
                        Err(e) => return Err(ReadCharError { bytes: to_utf8(item, tail_bytes_count, tail_byte_index), io_error: e }),
                        Ok(buf) => {
                            if buf.is_empty() {
                                return Err(ReadCharError { bytes: to_utf8(item, tail_bytes_count, tail_byte_index), io_error: io::Error::from(io::ErrorKind::UnexpectedEof) });
                            }
                            if buf[0] & TAIL_BYTE_MASK != TAIL_BYTE_PATTERN {
                                return Err(ReadCharError { bytes: to_utf8(item, tail_bytes_count, tail_byte_index), io_error: io::Error::from(io::ErrorKind::InvalidData) });
                            }
                            item |= ((buf[0] & !TAIL_BYTE_MASK) as u32) << ((tail_bytes_count - 1 - tail_byte_index) * TAIL_BYTE_VALUE_BITS);
                            self.consume(1);
                        }
                    }
                }
                if item < SEQUENCE_MIN_VALUE[tail_bytes_count as usize] {
                    return Err(ReadCharError { bytes: to_utf8(item, tail_bytes_count, tail_bytes_count), io_error: io::Error::from(io::ErrorKind::InvalidData) });
                }
                match char::from_u32(item) {
                    None => Err(ReadCharError { bytes: to_utf8(item, tail_bytes_count, tail_bytes_count), io_error: io::Error::from(io::ErrorKind::InvalidData) }),
                    Some(item) => Ok(Some(item))
                }
            }
        }
    }
}

impl<T: BufRead + ?Sized> BufReadCharsExt for T { }

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
        let bytes: &mut dyn BufRead = &mut BufReader::new("ABcd АБвгд UV".as_bytes());
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
        assert_eq!(&[0xF5, 0x8F, 0xBF, 0xBF][..], err.as_bytes());
    }

    #[test]
    fn read_surrogate() {
        let mut bytes = BufReader::new(&[ 0xED, 0xA0, 0x80 ][..]);
        let res = bytes.chars().collect::<Vec<_>>();
        assert_eq!(1, res.len());
        let err = res[0].as_ref().err().unwrap();
        assert_eq!(&[0xED, 0xA0, 0x80][..], err.as_bytes());
    }

    #[test]
    fn read_invalid_sequences() {
        let mut bytes = BufReader::new(&[ 0x81, 0x82, 0xC1, 0x07, 0xC1, 0x87, 0xC2, 0xC2, 0x82, 0xF7, 0x88, 0x89, 0x07 ][..]);
        let res = bytes.chars().collect::<Vec<_>>();
        assert_eq!(9, res.len());
        assert_eq!(&[0x81][..], res[0].as_ref().err().unwrap().as_bytes());
        assert_eq!(&[0x82][..], res[1].as_ref().err().unwrap().as_bytes());
        assert_eq!(&[0xC1][..], res[2].as_ref().err().unwrap().as_bytes());
        assert_eq!('\x07', *res[3].as_ref().unwrap());
        assert_eq!(&[0xC1, 0x87][..], res[4].as_ref().err().unwrap().as_bytes());
        assert_eq!(&[0xC2][..], res[5].as_ref().err().unwrap().as_bytes());
        assert_eq!('\u{82}', *res[6].as_ref().unwrap());
        assert_eq!(&[0xF7, 0x88, 0x89][..], res[7].as_ref().err().unwrap().as_bytes());
        assert_eq!('\x07', *res[8].as_ref().unwrap());
    }

    #[quickcheck]
    fn read_string(s: String) -> bool {
        let mut t = String::new();
        BufReader::new(s.as_bytes()).chars().for_each(|c| t.push(c.unwrap()));
        s == t
    }

    #[quickcheck]
    fn read_array(b: Vec<u8>) -> bool {
        let mut t = Vec::new();
        BufReader::new(&b[..]).chars().for_each(|c| t.append(&mut c.map_or_else(|e| e.as_bytes().to_vec(), |s| s.to_string().as_bytes().to_vec())));
        b == t
    }
}
