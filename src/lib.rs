#![allow(non_shorthand_field_patterns)]
extern crate arrayvec;

pub mod utf_chars {
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
    pub struct Utf8CharsError(ArrayVec<[u8; UTF8_SEQUENCE_MAX_LENGTH as usize]>);
    impl Utf8CharsError {
        pub fn as_bytes(&self) -> &[u8] { &self.0 }
        pub fn into_bytes(self) -> ArrayVec<[u8; UTF8_SEQUENCE_MAX_LENGTH as usize]> { self.0 }
    }
    impl fmt::Display for Utf8CharsError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "invalid UTF-8 byte sequence")?;
            for b in &self.0 {
                write!(f, " {:02X}", b)?;
            }
            Ok(())
        }
    }
    
    const UTF8_SEQUENCE_MAX_LENGTH: u8 = 4;
    const LEADING_BYTE_MASK: [u8; UTF8_SEQUENCE_MAX_LENGTH as usize] = [0x80, 0xE0, 0xF0, 0xF8];
    const LEADING_BYTE_PATTERN: [u8; UTF8_SEQUENCE_MAX_LENGTH as usize] = [0x00, 0xC0, 0xE0, 0xF0];
    const TAIL_BYTE_MASK: u8 = 0xC0;
    const TAIL_BYTE_PATTERN: u8 = 0x80;
    const TAIL_BYTE_VALUE_BITS: u8 = 6;
    fn to_utf8(item: u32, expected_tail_bytes_count: u8, actual_tail_bytes_count: u8) -> ArrayVec<[u8; UTF8_SEQUENCE_MAX_LENGTH as usize]> {
        let mut res = ArrayVec::new();
        let leading_byte = LEADING_BYTE_PATTERN[expected_tail_bytes_count as usize] |
                            ((item >> (TAIL_BYTE_VALUE_BITS * expected_tail_bytes_count)) as u8) & !LEADING_BYTE_MASK[expected_tail_bytes_count as usize];
        res.push(leading_byte);
        for tail_byte_index in 0..actual_tail_bytes_count {
            res.push(TAIL_BYTE_PATTERN | ((item >> ((expected_tail_bytes_count - 1 - tail_byte_index) * TAIL_BYTE_VALUE_BITS)) as u8) & !TAIL_BYTE_MASK);
        }
        res
    }
    impl<'a, T: BufRead> Iterator for Utf8Chars<'a, T> {
        type Item = Result<char, (Utf8CharsError, Option<io::Error>)>;

        fn next(&mut self) -> Option<Self::Item> {
            match self.0.fill_buf() {
                Err(e) => return Some(Err((Utf8CharsError(ArrayVec::new()), Some(e)))),
                Ok(buf) => {
                    if buf.is_empty() { return None; }
                    let leading_byte = buf[0];
                    self.0.consume(1);
                    let tail_bytes_count = 'r: loop {
                        for i in 0..UTF8_SEQUENCE_MAX_LENGTH {
                            if leading_byte & LEADING_BYTE_MASK[i as usize] == LEADING_BYTE_PATTERN[i as usize] { break 'r i; }
                        }
                        let mut bytes = ArrayVec::new();
                        bytes.push(leading_byte);
                        return Some(Err((Utf8CharsError(bytes), None)));
                    };
                    let mut item = ((leading_byte & !LEADING_BYTE_MASK[tail_bytes_count as usize]) as u32) << (TAIL_BYTE_VALUE_BITS * tail_bytes_count);
                    for tail_byte_index in 0..tail_bytes_count {
                        match self.0.fill_buf() {
                            Err(e) => return Some(Err((Utf8CharsError(to_utf8(item, tail_bytes_count, tail_byte_index)), Some(e)))),
                            Ok(buf) => {
                                if buf.is_empty() || buf[0] & TAIL_BYTE_MASK != TAIL_BYTE_PATTERN {
                                    return Some(Err((Utf8CharsError(to_utf8(item, tail_bytes_count, tail_byte_index)), None)));
                                }
                                item |= ((buf[0] & !TAIL_BYTE_MASK) as u32) << ((tail_bytes_count - 1 - tail_byte_index) * TAIL_BYTE_VALUE_BITS);
                                self.0.consume(1);
                            }
                        }
                    }
                    match char::from_u32(item) {
                        None => Some(Err((Utf8CharsError(to_utf8(item, tail_bytes_count, tail_bytes_count)), None))),
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
        /// The iterator returned from this function will yield instances of `Result<char, (Utf8CharsError, Option<io::Error>)>`.
        /// The `Err` variant contains invalid ot incomplete char with optional I/O error.
        /// An `Utf8CharsError` can contains empty byte sequence if I/O error occurs when read a leading byte.
        fn utf8_chars<'a>(&'a mut self) -> Utf8Chars<'a, Self>;
    }
    impl<T: BufRead> ReadChars for T {
        fn utf8_chars<'a>(&'a mut self) -> Utf8Chars<'a, Self> { Utf8Chars(self) }
    }

    #[cfg(test)]
    mod tests {
        use std::io::{BufRead, BufReader};
        use std::vec::{Vec};
        use crate::utf_chars::{ReadChars};

        #[test]
        fn read_valid_unicode() {
            assert_eq!(vec!['A', 'B', 'c', 'd', ' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', 'V'],
                        BufReader::new("ABcd АБвгд UV".as_bytes()).utf8_chars().map(|x| x.unwrap()).collect::<Vec<_>>());
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
    }
}
