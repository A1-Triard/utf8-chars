#![allow(non_shorthand_field_patterns)]
extern crate arrayvec;

use std::{fmt};
use std::char::{self};
use std::io::{self, BufRead};
use arrayvec::{ArrayVec};

/// An iterator over the chars of an instance of `BufRead` containing UTF-8 encoded text.
///
/// This struct is generally created by calling `utf8_chars` on a `BufRead`.
#[derive(Debug)]
pub struct Utf8Chars<'a, T: BufRead + ?Sized>(&'a mut T);

/// A byte sequence, representing an invalid or incomplete UTF-8 char.
#[derive(Debug)]
pub struct Utf8InvalidSequence(ArrayVec<[u8; UTF8_SEQUENCE_MAX_LENGTH as usize]>);
impl Utf8InvalidSequence {
    pub fn as_bytes(&self) -> &[u8] { &self.0 }
    pub fn into_bytes(self) -> ArrayVec<[u8; UTF8_SEQUENCE_MAX_LENGTH as usize]> { self.0 }
}
impl fmt::Display for Utf8InvalidSequence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid UTF-8 byte sequence")?;
        for b in &self.0 {
            write!(f, " {:02X}", b)?;
        }
        Ok(())
    }
}

const UTF8_SEQUENCE_MAX_LENGTH: u8 = 4;
const UTF8_LEAD_BYTE_MASK: [u8; UTF8_SEQUENCE_MAX_LENGTH as usize] = [0x80, 0xE0, 0xF0, 0xF8];
const UTF8_LEAD_BYTE_PATTERN: [u8; UTF8_SEQUENCE_MAX_LENGTH as usize] = [0x00, 0xC0, 0xE0, 0xF0];
const UTF8_TAIL_BYTE_MASK: u8 = 0xC0;
const UTF8_TAIL_BYTE_PATTERN: u8 = 0x80;
const UTF8_TAIL_BYTE_VALUE_BITS: u8 = 6;
const UTF8_NONZERO_BITS_MASK: [u32; UTF8_SEQUENCE_MAX_LENGTH as usize] = [0, 0x0780, 0xF800, 0x01F00000];
fn to_utf8(item: u32, expected_tail_bytes_count: u8, actual_tail_bytes_count: u8) -> ArrayVec<[u8; UTF8_SEQUENCE_MAX_LENGTH as usize]> {
    let mut res = ArrayVec::new();
    let lead_byte = UTF8_LEAD_BYTE_PATTERN[expected_tail_bytes_count as usize] |
                        ((item >> (UTF8_TAIL_BYTE_VALUE_BITS * expected_tail_bytes_count)) as u8) & !UTF8_LEAD_BYTE_MASK[expected_tail_bytes_count as usize];
    res.push(lead_byte);
    for tail_byte_index in 0..actual_tail_bytes_count {
        res.push(UTF8_TAIL_BYTE_PATTERN | ((item >> ((expected_tail_bytes_count - 1 - tail_byte_index) * UTF8_TAIL_BYTE_VALUE_BITS)) as u8) & !UTF8_TAIL_BYTE_MASK);
    }
    res
}
impl<'a, T: BufRead> Iterator for Utf8Chars<'a, T> {
    type Item = Result<char, (Utf8InvalidSequence, Option<io::Error>)>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.fill_buf() {
            Err(e) => return Some(Err((Utf8InvalidSequence(ArrayVec::new()), Some(e)))),
            Ok(buf) => {
                if buf.is_empty() { return None; }
                let lead_byte = buf[0];
                self.0.consume(1);
                let tail_bytes_count = 'r: loop {
                    for i in 0..UTF8_SEQUENCE_MAX_LENGTH {
                        if lead_byte & UTF8_LEAD_BYTE_MASK[i as usize] == UTF8_LEAD_BYTE_PATTERN[i as usize] { break 'r i; }
                    }
                    let mut bytes = ArrayVec::new();
                    bytes.push(lead_byte);
                    return Some(Err((Utf8InvalidSequence(bytes), None)));
                };
                let mut item = ((lead_byte & !UTF8_LEAD_BYTE_MASK[tail_bytes_count as usize]) as u32) << (UTF8_TAIL_BYTE_VALUE_BITS * tail_bytes_count);
                for tail_byte_index in 0..tail_bytes_count {
                    match self.0.fill_buf() {
                        Err(e) => return Some(Err((Utf8InvalidSequence(to_utf8(item, tail_bytes_count, tail_byte_index)), Some(e)))),
                        Ok(buf) => {
                            if buf.is_empty() || buf[0] & UTF8_TAIL_BYTE_MASK != UTF8_TAIL_BYTE_PATTERN {
                                return Some(Err((Utf8InvalidSequence(to_utf8(item, tail_bytes_count, tail_byte_index)), None)));
                            }
                            item |= ((buf[0] & !UTF8_TAIL_BYTE_MASK) as u32) << ((tail_bytes_count - 1 - tail_byte_index) * UTF8_TAIL_BYTE_VALUE_BITS);
                            self.0.consume(1);
                        }
                    }
                }
                if tail_bytes_count != 0 && item & UTF8_NONZERO_BITS_MASK[tail_bytes_count as usize] == 0 {
                    return Some(Err((Utf8InvalidSequence(to_utf8(item, tail_bytes_count, tail_bytes_count)), None)));
                }
                match char::from_u32(item) {
                    None => Some(Err((Utf8InvalidSequence(to_utf8(item, tail_bytes_count, tail_bytes_count)), None))),
                    Some(item) => Some(Ok(item))
                }
            }
        }
    }
}
/// An extension trait, allowing char-per-char read from `BufRead`.
pub trait ReadChars : BufRead {
    /// Returns an iterator over the chars of this reader containing UTF-8 encoded text.
    ///
    /// The iterator returned from this function will yield instances of `Result<char, (Utf8InvalidSequence, Option<io::Error>)>`.
    /// The `Err` variant contains an invalid ot incomplete char with an optional I/O error.
    /// The `Utf8InvalidSequence` can contain an empty byte sequence if an I/O error occurs when read a lead byte.
    fn utf8_chars<'a>(&'a mut self) -> Utf8Chars<'a, Self>;
}
impl<T: BufRead> ReadChars for T {
    fn utf8_chars<'a>(&'a mut self) -> Utf8Chars<'a, Self> { Utf8Chars(self) }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, BufReader};
    use std::vec::{Vec};
    use crate::{ReadChars};

    #[test]
    fn read_valid_unicode() {
        assert_eq!(vec!['A', 'B', 'c', 'd', ' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', '\0'],
                    BufReader::new("ABcd АБвгд U\0".as_bytes()).utf8_chars().map(|x| x.unwrap()).collect::<Vec<_>>());
    }

    #[test]
    fn read_valid_unicode_from_dyn_read() {
        let mut bytes: &mut dyn BufRead = &mut BufReader::new("ABcd АБвгд UV".as_bytes());
        assert_eq!(vec!['A', 'B', 'c', 'd', ' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', 'V'], bytes.utf8_chars().map(|x| x.unwrap()).collect::<Vec<_>>());
    }

    #[test]
    fn do_not_take_extra_bytes() {
        let mut bytes = BufReader::new("ABcd АБвгд UV".as_bytes());
        assert_eq!(vec!['A', 'B', 'c', 'd'], bytes.utf8_chars().take(4).map(|x| x.unwrap()).collect::<Vec<_>>());
        assert_eq!(vec![' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', 'V'], bytes.utf8_chars().map(|x| x.unwrap()).collect::<Vec<_>>());
    }

    #[test]
    fn read_value_out_of_range() {
        let mut bytes = BufReader::new(&[ 0xF5, 0x8F, 0xBF, 0xBF ][..]);
        let res = bytes.utf8_chars().collect::<Vec<_>>();
        assert_eq!(1, res.len());
        let err = res[0].as_ref().err().unwrap();
        assert_eq!(&[0xF5, 0x8F, 0xBF, 0xBF][..], err.0.as_bytes());
    }

    #[test]
    fn read_invalid_sequences() {
        let mut bytes = BufReader::new(&[ 0x81, 0x82, 0xC1, 0x07, 0xC1, 0x87, 0xC2, 0xC2, 0x82, 0xF7, 0x88, 0x89, 0x07 ][..]);
        let res = bytes.utf8_chars().collect::<Vec<_>>();
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
