// Copyright 2021-2023 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of bsn1
//
//  bsn1 is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  bsn1 is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with bsn1.  If not, see <http://www.gnu.org/licenses/>.
//
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! functions and enum about 'Length' octet of 'ASN.1.'

use crate::{Error, LengthBuffer};
use std::cmp::Ordering;
use std::io::{Read, Write};
use std::mem::{size_of, size_of_val};
use std::ops::Deref;

/// `Length` represents ASN.1 length.
///
/// Note that `Length` represents the byte count of the contents in ASN.1.
/// The total byte size of BER, DER, and CER is greater than that.
/// (BER, DER, and CER are constituted of identifier, length, and contents.)
#[derive(Debug, Clone, Copy, Hash)]
pub enum Length {
    /// Represents 'Indefinite' length.
    ///
    /// 'Indefinite' is only for 'BER', and the contents must end with 'EOC' octets.
    Indefinite,
    /// 'Definite' is for 'BER', 'DER', and 'CER', and represents the byte count of the contents.
    Definite(usize),
}

impl PartialEq for Length {
    fn eq(&self, other: &Self) -> bool {
        self.is_definite() && self.definite() == other.definite()
    }
}

impl PartialOrd for Length {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let this = self.definite()?;
        let other = other.definite()?;

        Some(this.cmp(&other))
    }
}

impl Length {
    const LONG_FLAG: u8 = 0x80;
    const MAX_SHORT: u8 = Self::LONG_FLAG - 1;
    const INDEFINITE: u8 = 0x80;
}

impl Length {
    /// Parses `readable` starting with length octets and tries to creates a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    ///
    /// // Serializes Definite(5).
    /// let length = Length::Definite(5);
    /// let mut serialized = Vec::from(&length.to_bytes()[..]);
    ///
    /// // Parses the serialized bytes.
    /// let deserialized = Length::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(length, deserialized);
    ///
    /// // The extra octets at the end does not affect the result.
    /// serialized.push(0x03);
    /// serialized.push(0x04);
    /// let deserialized = Length::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(length, deserialized);
    /// ```
    pub fn parse<R: Read>(readable: &mut R) -> Result<Self, Error> {
        let mut writeable = std::io::sink();
        unsafe { parse_length(readable, &mut writeable) }
    }

    /// Serializes `length`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    ///
    /// // Serializes Definite(3), and deserializes it.
    /// // The result is Definite(3).
    /// let bytes = Length::Definite(3).to_bytes();
    /// let deserialized = Length::parse(&mut &*bytes).unwrap();
    /// assert_eq!(Length::Definite(3), deserialized);
    /// ```
    pub fn to_bytes(self) -> impl Deref<Target = [u8]> {
        let mut buffer = LengthBuffer::new();

        match self {
            Length::Indefinite => unsafe { buffer.push(Length::INDEFINITE) },
            Length::Definite(val) => {
                if val <= Length::MAX_SHORT as usize {
                    // Short form
                    unsafe { buffer.push(val as u8) };
                } else {
                    // Long form
                    const BITS_PER_BYTE: usize = 8;
                    let bit_len =
                        BITS_PER_BYTE * size_of::<usize>() - (val.leading_zeros() as usize);
                    let byte_len = (bit_len + BITS_PER_BYTE - 1) / BITS_PER_BYTE;
                    let flag = Length::LONG_FLAG + byte_len as u8;

                    unsafe {
                        buffer.set_len(byte_len + size_of_val(&flag));
                        buffer[0] = flag;

                        let val = val.to_be();
                        let src = &val as *const usize;
                        let src = src as *const u8;
                        let src = src.add(size_of::<usize>() - byte_len);

                        let dst = buffer.as_mut_ptr().add(size_of_val(&flag));
                        dst.copy_from_nonoverlapping(src, byte_len);
                    }
                }
            }
        }

        buffer
    }

    /// Returns the byte count of the octets that `self` is serialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    ///
    /// // The length of INDEFINITE is always 1.
    /// assert_eq!(Length::Indefinite.len(), 1);
    ///
    /// // The length is 1 if the value is less than or equals to 127.
    /// assert_eq!(Length::Definite(0).len(), 1);
    /// assert_eq!(Length::Definite(127).len(), 1);
    ///
    /// // The length is 2 if the value is 128.
    /// assert_eq!(Length::Definite(128).len(), 2);
    /// ```
    pub const fn len(self) -> usize {
        match self {
            Length::Indefinite => 1,
            Length::Definite(val) => {
                if val <= Length::MAX_SHORT as usize {
                    1
                } else {
                    const BITS_PER_BYTE: usize = 8;
                    let bit_len =
                        BITS_PER_BYTE * size_of::<usize>() - (val.leading_zeros() as usize);
                    let byte_len = (bit_len + (BITS_PER_BYTE - 1)) / BITS_PER_BYTE;

                    const FLAG_LEN: usize = 1;
                    byte_len + FLAG_LEN
                }
            }
        }
    }

    /// Converts `self` to `Option<usize>`.
    ///
    /// Returns `None` if self is `Indefinite`; otherwise, wraps the inner number in `Some`
    /// and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    ///
    /// let length = Length::Indefinite;
    /// assert_eq!(length.definite(), None);
    ///
    /// let length = Length::Definite(45);
    /// assert_eq!(length.definite(), Some(45));
    /// ```
    pub fn definite(self) -> Option<usize> {
        match self {
            Self::Indefinite => None,
            Self::Definite(n) => Some(n),
        }
    }

    /// Returns `true` if `self` is `Indefinite`; otherwise `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    ///
    /// let length = Length::Indefinite;
    /// assert_eq!(length.is_indefinite(), true);
    ///
    /// let length = Length::Definite(12);
    /// assert_eq!(length.is_indefinite(), false);
    /// ```
    pub fn is_indefinite(self) -> bool {
        match self {
            Self::Indefinite => true,
            _ => false,
        }
    }

    /// Returns `false` if `self` is `Indefinite`; otherwise `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    ///
    /// let length = Length::Indefinite;
    /// assert_eq!(length.is_definite(), false);
    ///
    /// let length = Length::Definite(12);
    /// assert_eq!(length.is_definite(), true);
    /// ```
    pub fn is_definite(self) -> bool {
        match self {
            Self::Indefinite => false,
            _ => true,
        }
    }
}

/// Parses `readable` starting with 'length', writes the parsed octets to `writeable`,
/// and returns `Length`.
///
/// # Safety
///
/// The behavior is undefined if `writeable` is closed or broken before this function returns.
/// `writeable` should be `std::io::Sink` or `Buffer`.
pub unsafe fn parse_length<R: Read, W: Write>(
    readable: &mut R,
    writeable: &mut W,
) -> Result<Length, Error> {
    use crate::misc::{read_u8, write_u8};

    let first = read_u8(readable)?;
    write_u8(writeable, first)?;

    if first == Length::INDEFINITE {
        // Indefinite
        Ok(Length::Indefinite)
    } else if first & Length::LONG_FLAG != Length::LONG_FLAG {
        // Short form
        Ok(Length::Definite(first as usize))
    } else {
        // Long form
        let second = read_u8(readable)?;
        if second == 0x00 {
            // The second octet is not necessary.
            return Err(Error::RedundantBytes);
        }
        write_u8(writeable, second)?;

        let followings_count = (first ^ Length::LONG_FLAG) as usize;
        if followings_count == 1 && second <= Length::MAX_SHORT {
            // Short form will do.
            return Err(Error::RedundantBytes);
        }
        if size_of::<usize>() < followings_count {
            return Err(Error::OverFlow);
        }

        let mut len = second as usize;
        for _ in 1..followings_count {
            let byte = read_u8(readable)?;
            write_u8(writeable, byte)?;
            len = (len << 8) + byte as usize;
        }

        Ok(Length::Definite(len))
    }
}

/// Parse `bytes` starting with 'length' and returns `(Length, octets_after_length)`.
///
/// # Safety
///
/// The behaviour is undefined if `bytes` does not start with Length octet(s).
pub unsafe fn from_bytes_starts_with_unchecked(bytes: &[u8]) -> (Length, &[u8]) {
    let first = bytes[0];
    let bytes = &bytes[1..];

    if first == Length::INDEFINITE {
        // Indefinite
        (Length::Indefinite, bytes)
    } else if first & Length::LONG_FLAG != Length::LONG_FLAG {
        // Short form
        (Length::Definite(first as usize), bytes)
    } else {
        // Long form
        let followings_count = (first & !Length::LONG_FLAG) as usize;

        let mut len: usize = 0;
        let src = bytes.as_ptr();
        let dst = (&mut len as *mut usize) as *mut u8;
        let dst = dst.add(size_of::<usize>() - followings_count);
        dst.copy_from_nonoverlapping(src, followings_count);

        let len = usize::from_be(len);
        let bytes = &bytes[followings_count..];
        (Length::Definite(len), bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod parse {
        use super::*;

        #[test]
        fn indefinite_without_extra_octet() {
            let mut bytes: &[u8] = &[0x80];
            let mut writeable = Vec::new();
            let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

            assert_eq!(length.is_indefinite(), true);
            assert_eq!(&writeable[..], &[0x80]);
            assert!(bytes.is_empty());
        }

        #[test]
        fn indefinite_and_extra_octet() {
            for i in 0..=u8::MAX {
                let mut bytes: &[u8] = &[0x80, i];
                let mut writeable = Vec::new();
                let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                assert_eq!(length.is_indefinite(), true);
                assert_eq!(&writeable[..], &[0x80]);
                assert_eq!(bytes, &[i]);
            }
        }

        #[test]
        fn short_form_without_extra_octet() {
            for i in 0..=Length::MAX_SHORT {
                let mut bytes: &[u8] = &[i];
                let mut writeable = Vec::new();
                let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                assert_eq!(length, Length::Definite(i as usize));
                assert_eq!(&writeable[..], &[i]);
                assert!(bytes.is_empty());
            }
        }

        #[test]
        fn short_form_and_extra_octet() {
            for i in 0..=Length::MAX_SHORT {
                for j in 0..=u8::MAX {
                    let mut bytes: &[u8] = &[i, j];
                    let mut writeable = Vec::new();
                    let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                    assert_eq!(length, Length::Definite(i as usize));
                    assert_eq!(&writeable[..], &[i]);
                    assert_eq!(bytes, &[j]);
                }
            }
        }

        #[test]
        fn two_bytes_without_extra_octet() {
            for i in Length::MAX_SHORT + 1..=u8::MAX {
                let mut bytes: &[u8] = &[0x81, i];
                let mut writeable = Vec::new();
                let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                assert_eq!(length, Length::Definite(i as usize));
                assert_eq!(&writeable[..], &[0x81, i]);
                assert!(bytes.is_empty());
            }
        }

        #[test]
        fn two_bytes_and_extra_octet() {
            for i in Length::MAX_SHORT + 1..=u8::MAX {
                for j in 0..=u8::MAX {
                    let mut bytes: &[u8] = &[0x81, i, j];
                    let mut writeable = Vec::new();
                    let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                    assert_eq!(length, Length::Definite(i as usize));
                    assert_eq!(&writeable[..], &[0x81, i]);
                    assert_eq!(bytes, &[j]);
                }
            }
        }

        #[test]
        fn three_bytes_without_extra_octet() {
            for &i in &[0x0100_usize, 0xffff_usize] {
                let i0 = (i >> 8) as u8;
                let i1 = i as u8;

                let mut bytes: &[u8] = &[0x82, i0, i1];
                let mut writeable = Vec::new();
                let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                assert_eq!(length, Length::Definite(i));
                assert_eq!(&writeable[..], &[0x82, i0, i1]);
                assert!(bytes.is_empty());
            }
        }

        #[test]
        fn three_bytes_and_extra_octet() {
            for &i in &[0x0100_usize, 0xffff_usize] {
                for j in 0..=u8::MAX {
                    let i0 = (i >> 8) as u8;
                    let i1 = i as u8;

                    let mut bytes: &[u8] = &[0x82, i0, i1, j];
                    let mut writeable = Vec::new();
                    let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                    assert_eq!(length, Length::Definite(i));
                    assert_eq!(&writeable[..], &[0x82, i0, i1]);
                    assert_eq!(bytes, &[j]);
                }
            }
        }

        #[test]
        fn max_without_extra_octet() {
            let mut bytes_org = [0xff; size_of::<usize>() + 1];
            bytes_org[0] = 0x80 + (size_of::<usize>() as u8);
            let mut bytes = &bytes_org as &[u8];

            let mut writeable = Vec::new();
            let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

            assert_eq!(length, Length::Definite(usize::MAX));
            assert_eq!(&writeable[..], &bytes_org[..]);
            assert!(bytes.is_empty());
        }

        #[test]
        fn max_and_extra_octet() {
            for j in 0..=u8::MAX {
                let mut bytes_org = [0xff; size_of::<usize>() + 2];
                bytes_org[0] = 0x80 + (size_of::<usize>() as u8);
                *bytes_org.last_mut().unwrap() = j;
                let mut bytes = &bytes_org as &[u8];

                let mut writeable = Vec::new();
                let length = unsafe { parse_length(&mut bytes, &mut writeable).unwrap() };

                assert_eq!(length, Length::Definite(usize::MAX));
                assert_eq!(&writeable[..], &bytes_org[..bytes_org.len() - 1]);
                assert_eq!(bytes, &[j]);
            }
        }

        #[test]
        fn overflow() {
            for i in 1..=u8::MAX {
                for j in 0..=u8::MAX {
                    let mut bytes: [u8; size_of::<usize>() + 2] = [j; size_of::<usize>() + 2];
                    bytes[0] = 0x80 + (size_of::<usize>() as u8) + 1;
                    bytes[1] = i;

                    let mut writeable = Vec::new();
                    let err = unsafe { parse_length(&mut &bytes[..], &mut writeable) };
                    assert_eq!(Error::OverFlow, err.unwrap_err());
                }
            }
        }

        #[test]
        fn long_form_for_small_length() {
            for i in 0..=Length::MAX_SHORT {
                let mut bytes: &[u8] = &[0x81, i];
                let mut writeable = Vec::new();

                let err = unsafe { parse_length(&mut bytes, &mut writeable).unwrap_err() };
                assert_eq!(err, Error::RedundantBytes);
            }
        }

        #[test]
        fn long_form_starting_with_0x00() {
            for i in 0..=u8::MAX {
                for j in 3..10 {
                    let mut bytes: Vec<u8> = std::iter::repeat(i).take(j as usize).collect();
                    bytes[0] = 0x80 + j - 1;
                    bytes[1] = 0x00;
                    let mut writeable = Vec::new();

                    let err = unsafe { parse_length(&mut &bytes[..], &mut writeable).unwrap_err() };
                    assert_eq!(err, Error::RedundantBytes);
                }
            }
        }

        #[test]
        fn unterminated() {
            for i in (0..=(i8::MAX as usize + 1)).chain(Some(usize::MAX)) {
                let length = Length::Definite(i);
                let bytes = Vec::from(&*length.to_bytes());

                let mut writeable = Vec::new();
                let mut bytes: &[u8] = &bytes[..bytes.len() - 1];
                let err = unsafe { parse_length(&mut bytes, &mut writeable).unwrap_err() };
                assert_eq!(err, Error::UnTerminatedBytes);
            }
        }
    }

    mod to_bytes {
        use super::*;

        #[test]
        fn indefinite() {
            let bytes = Length::Indefinite.to_bytes();
            assert_eq!(&bytes[..], &[0x80]);
        }

        #[test]
        fn definite() {
            for i in (0..=(u8::MAX as usize + 1)).chain(Some(usize::MAX)) {
                let length = Length::Definite(i);
                let bytes = length.to_bytes();

                let mut writeable = Vec::new();
                let mut readable: &[u8] = &bytes[..];
                let deserialized = unsafe { parse_length(&mut readable, &mut writeable).unwrap() };

                assert_eq!(length, deserialized);
                assert_eq!(&bytes[..], &writeable[..]);
            }
        }
    }

    #[test]
    fn len() {
        // Indefinite
        assert_eq!(Length::Indefinite.len(), 1);

        // Definite 1 byte
        for i in 0..128 {
            assert_eq!(Length::Definite(i).len(), 1);
        }

        // Definite 2 byte
        assert_eq!(Length::Definite(128).len(), 2);
        assert_eq!(Length::Definite(255).len(), 2);

        // Definite 3 byte
        assert_eq!(Length::Definite(257).len(), 3);
        assert_eq!(Length::Definite(65535).len(), 3);

        // Max
        assert_eq!(
            Length::Definite(std::usize::MAX).len(),
            std::mem::size_of::<usize>() + 1
        );
    }
}
