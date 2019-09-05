#![feature(ptr_offset_from)]
#![allow(non_shorthand_field_patterns)]
extern crate utf8;
extern crate arrayvec;

pub mod utf8_chars {
    use std::{fmt};
    use std::error::{Error};
    use std::io::{self, Read};
    use std::mem::{replace};
    use arrayvec::{ArrayVec};

    const BUFFER_SIZE: usize = 16;

    #[derive(Debug)]
    pub struct Chars<'a, T: Read + ?Sized> {
        input: &'a mut T,
        byte_buffer: [u8; BUFFER_SIZE],
        byte_buffer_start: usize,
        byte_buffer_end: usize,
        incomplete_sequence_buffer: utf8::Incomplete,
        char_buffer: [char; BUFFER_SIZE],
        char_buffer_start: usize,
        char_buffer_end: usize,
        invalid_sequence_buffer: ArrayVec<[u8; 6]>,
    }
    #[derive(Debug)]
    pub struct CharsError {
        bytes: ArrayVec<[u8; 6]>,
    }
    impl CharsError {
        pub fn as_bytes(&self) -> &[u8] { &self.bytes }
        pub fn into_bytes(self) -> ArrayVec<[u8; 6]> { self.bytes }
    }
    impl Error for CharsError {
        fn description(&self) -> &str {
            "invalid utf-8 byte sequence"
        }
    }
    impl fmt::Display for CharsError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "invalid utf-8 byte sequence")?;
            for b in &self.bytes {
                write!(f, " {:02X}", b)?;
            }
            Ok(())
        }
    }
    impl<'a, T: Read> Iterator for Chars<'a, T> {
        type Item = io::Result<char>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if self.char_buffer_start < self.char_buffer_end {
                    let item = self.char_buffer[self.char_buffer_start];
                    self.char_buffer_start += 1;
                    return Some(Ok(item));
                }
                if !self.invalid_sequence_buffer.is_empty() {
                    return Some(Err(io::Error::new(io::ErrorKind::InvalidData, CharsError { bytes: replace(&mut self.invalid_sequence_buffer, ArrayVec::new()) })));
                }
                if self.byte_buffer_start >= self.byte_buffer_end {
                    match self.input.read(&mut self.byte_buffer) {
                        Err(e) => return Some(Err(e)),
                        Ok(readed) => {
                            self.byte_buffer_start = 0;
                            self.byte_buffer_end = readed;
                        }
                    }
                    if self.byte_buffer_end == 0 {
                        if self.incomplete_sequence_buffer.is_empty() { return None; }
                        let incomplete_sequence = self.incomplete_sequence_buffer.try_complete(&[0_u8]).unwrap().0.err().unwrap();
                        return Some(Err(io::Error::new(io::ErrorKind::InvalidData, CharsError { bytes: incomplete_sequence.iter().map(|x| *x).collect() })));
                    }
                }
                let (chars, invalid_sequence, remaining_input) = if self.incomplete_sequence_buffer.is_empty() {
                    match utf8::decode(&self.byte_buffer[self.byte_buffer_start .. self.byte_buffer_end]) {
                        Ok(chars) => (chars, &[][..], &self.byte_buffer[self.byte_buffer_end .. self.byte_buffer_end]),
                        Err(utf8::DecodeError::Incomplete { valid_prefix: chars, incomplete_suffix: incomplete_suffix }) => {
                            self.incomplete_sequence_buffer = incomplete_suffix;
                            (chars, &[][..], &self.byte_buffer[self.byte_buffer_end .. self.byte_buffer_end])
                        },
                        Err(utf8::DecodeError::Invalid { valid_prefix: chars, invalid_sequence: invalid_sequence, remaining_input: remaining_input }) => {
                            (chars, invalid_sequence, remaining_input)
                        }
                    }
                } else {
                    match self.incomplete_sequence_buffer.try_complete(&self.byte_buffer[self.byte_buffer_start .. self.byte_buffer_end]) {
                        None => ("", &[][..], &self.byte_buffer[self.byte_buffer_end .. self.byte_buffer_end]),
                        Some((Err(invalid_sequence), remaining_input)) => ("", invalid_sequence, remaining_input),
                        Some((Ok(chars), remaining_input)) => (chars, &[][..], remaining_input)
                    }
                };
                self.byte_buffer_start = unsafe { remaining_input.as_ptr().offset_from(self.byte_buffer.as_ptr()) as usize };
                let chars = chars.chars();
                self.char_buffer_start = 0;
                self.char_buffer_end = 0;
                for (buf, ch) in self.char_buffer.iter_mut().zip(chars) {
                    *buf = ch;
                    self.char_buffer_end += 1;
                }
                self.invalid_sequence_buffer = invalid_sequence.iter().map(|x| *x).collect();
            }
        }
    }
    pub trait ReadChars : Read {
        fn chars<'a>(&'a mut self) -> Chars<'a, Self>;
    }
    impl<T: Read> ReadChars for T {
        fn chars<'a>(&'a mut self) -> Chars<'a, Self> {
            Chars {
                input: self,
                byte_buffer: [0; BUFFER_SIZE],
                byte_buffer_start: 0,
                byte_buffer_end: 0,
                incomplete_sequence_buffer: utf8::Incomplete::empty(),
                char_buffer: ['\0'; BUFFER_SIZE],
                char_buffer_start: 0,
                char_buffer_end: 0,
                invalid_sequence_buffer: ArrayVec::new(),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use std::io::{Read};
        use std::vec::{Vec};
        use crate::utf8_chars::{ReadChars};

        #[test]
        fn it_works() {
            assert_eq!(vec!['A', 'B', 'c', 'd', ' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', 'V'], "ABcd АБвгд UV".as_bytes().chars().map(|x| x.unwrap()).collect::<Vec<_>>());
            let mut bytes: &mut dyn Read = &mut "ABcd АБвгд UV".as_bytes();
            assert_eq!(vec!['A', 'B', 'c', 'd', ' ', 'А', 'Б', 'в', 'г', 'д', ' ', 'U', 'V'], bytes.chars().map(|x| x.unwrap()).collect::<Vec<_>>());
        }
    }
}
