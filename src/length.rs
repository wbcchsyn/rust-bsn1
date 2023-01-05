// Copyright 2021-2022 Shin Yoshida
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

use crate::{Error, StackBuffer};
use std::convert::TryFrom;
use std::mem::{size_of, size_of_val};
use std::ops::Deref;

/// `Length` represents ASN.1 length.
///
/// Note that `Length` represents the byte count of the contents in ASN.1.
/// The total byte size of BER, DER, and CER is greater than that.
/// (BER, DER, and CER are constituted of identifier, length, and contents.)
#[derive(Debug, Clone, Copy, PartialEq, Hash)]
pub enum Length {
    /// Represents 'Indefinite' length.
    ///
    /// 'Indefinite' is only for 'BER', and the contents must end with 'EOC' octets.
    Indefinite,
    /// 'Definite' is for 'BER', 'DER', and 'CER', and represents the byte count of the contents.
    Definite(usize),
}

impl TryFrom<&[u8]> for Length {
    type Error = Error;

    /// Parses `bytes` starting with length octets and tries to create a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`try_from_bytes`].
    ///
    /// [`try_from_bytes`]: #method.from_bytes
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        try_from(bytes).map(|(length, _rest)| length)
    }
}

impl Length {
    const LONG_FLAG: u8 = 0x80;
    const MAX_SHORT: u8 = Self::LONG_FLAG - 1;
    const INDEFINITE: u8 = 0x80;
}

impl Length {
    /// Parses `bytes` starting with length octets and tries to creates a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This method is same to [`TryFrom`] implementation.
    ///
    /// [`TryFrom`]: #impl-TryFrom-for-Length
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    ///
    /// let mut bytes = vec![0x05]; // represents Definite(5).
    /// let len = Length::try_from_bytes(&bytes).unwrap();
    /// assert_eq!(Length::Definite(5), len);
    ///
    /// // Ignores the last extra octet 0x03.
    /// bytes.push(0x03);
    /// let len = Length::try_from_bytes(&bytes).unwrap();
    /// assert_eq!(Length::Definite(5), len);
    /// ```
    pub fn try_from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        try_from(bytes).map(|(length, _rest)| length)
    }

    /// Serializes `length` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Length;
    /// use std::convert::TryFrom;
    ///
    /// let length = Length::Definite(3);
    /// let bytes = length.to_bytes();
    ///
    /// let deserialized = Length::try_from(&bytes as &[u8]).unwrap();
    /// assert_eq!(length, deserialized);
    /// ```
    pub fn to_bytes(self) -> impl Deref<Target = [u8]> {
        let mut buffer = StackBuffer::new();

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
}

/// Tries to parse `bytes` starting with 'length' and returns `(Length, octets_after_length)`.
///
/// This function ignores extra octets at the end of `bytes` .
pub fn try_from(bytes: &[u8]) -> Result<(Length, &[u8]), Error> {
    let first = *bytes.get(0).ok_or(Error::UnTerminatedBytes)?;
    let bytes = &bytes[1..];

    if first == Length::INDEFINITE {
        // Indefinite
        Ok((Length::Indefinite, bytes))
    } else if first & Length::LONG_FLAG != Length::LONG_FLAG {
        // Short form
        Ok((Length::Definite(first as usize), bytes))
    } else {
        // Long form
        let second = *bytes.get(0).ok_or(Error::UnTerminatedBytes)?;
        if second == 0x00 {
            return Err(Error::RedundantBytes);
        }

        let followings_count = (first & !Length::LONG_FLAG) as usize;
        if bytes.len() < followings_count {
            return Err(Error::UnTerminatedBytes);
        }

        if size_of::<usize>() < followings_count {
            return Err(Error::OverFlow);
        }

        let mut len: usize = 0;
        unsafe {
            let src = bytes.as_ptr();
            let dst = (&mut len as *mut usize) as *mut u8;
            let dst = dst.add(size_of::<usize>() - followings_count);
            dst.copy_from_nonoverlapping(src, followings_count);
        }
        let len = usize::from_be(len);

        let bytes = &bytes[followings_count..];
        Ok((Length::Definite(len), bytes))
    }
}

/// Parse `bytes` starting with 'length' and returns `(Length, octets_after_length)` .
///
/// # Safety
///
/// The behavior is undefined if `bytes` does not start with Length octet(s).
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

    #[test]
    fn try_from_just() {
        let empty: &[u8] = &[];

        // Indefinite
        {
            let bytes: &[u8] = &[0x80];
            let res = try_from(bytes).unwrap();
            assert_eq!((Length::Indefinite, empty), res);
        }

        // Short form
        {
            let bytes: &[u8] = &[0x00];
            let res = try_from(bytes).unwrap();
            assert_eq!((Length::Definite(0), empty), res);

            let bytes: &[u8] = &[0x7f];
            let res = try_from(bytes).unwrap();
            assert_eq!((Length::Definite(0x7f), empty), res);
        }

        // 2 bytes
        {
            let bytes: &[u8] = &[0x81, 0x80];
            let res = try_from(bytes).unwrap();
            assert_eq!((Length::Definite(0x80), empty), res);

            let bytes: &[u8] = &[0x81, 0xff];
            let res = try_from(bytes).unwrap();
            assert_eq!((Length::Definite(0xff), empty), res);
        }

        // 3 bytes
        {
            let bytes: &[u8] = &[0x82, 0x01, 0x00];
            let res = try_from(bytes).unwrap();
            assert_eq!((Length::Definite(0x0100), empty), res);

            let bytes: &[u8] = &[0x82, 0xff, 0xff];
            let res = try_from(bytes).unwrap();
            assert_eq!((Length::Definite(0xffff), empty), res);
        }

        // max
        {
            let mut bytes: [u8; size_of::<usize>() + 1] = [0xff; size_of::<usize>() + 1];
            bytes[0] = 0x80 + (size_of::<usize>() as u8);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(std::usize::MAX), empty), res);
        }
    }

    #[test]
    fn try_from_extra() {
        let extra: &[u8] = &[1, 2, 3];

        // Indefinite
        {
            let mut bytes = vec![0x80];
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Indefinite, extra), res);
        }

        // Short form
        {
            let mut bytes = vec![0x00];
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(0), extra), res);

            let mut bytes = vec![0x7f];
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(0x7f), extra), res);
        }

        // 2 bytes
        {
            let mut bytes = vec![0x81, 0x80];
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(0x80), extra), res);

            let mut bytes = vec![0x81, 0xff];
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(0xff), extra), res);
        }

        // 3 bytes
        {
            let mut bytes = vec![0x82, 0x01, 0x00];
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(0x0100), extra), res);

            let mut bytes = vec![0x82, 0xff, 0xff];
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(0xffff), extra), res);
        }

        // max
        {
            let mut bytes: [u8; size_of::<usize>() + 1] = [0xff; size_of::<usize>() + 1];
            bytes[0] = 0x80 + (size_of::<usize>() as u8);
            let mut bytes = Vec::from(&bytes as &[u8]);
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(std::usize::MAX), extra), res);
        }
    }

    #[test]
    fn try_from_overflow() {
        let mut bytes: [u8; size_of::<usize>() + 2] = [0x00; size_of::<usize>() + 2];
        bytes[0] = 0x80 + (size_of::<usize>() as u8) + 1;
        bytes[1] = 0x01;
        let e = try_from(&bytes).unwrap_err();
        assert_eq!(Error::OverFlow, e);

        let mut bytes = Vec::from(&bytes as &[u8]);
        bytes.push(0xff);
        let e = try_from(&bytes).unwrap_err();
        assert_eq!(Error::OverFlow, e);
    }

    #[test]
    fn try_from_redundant() {
        // 2 bytes
        {
            let bytes: &[u8] = &[0x81, 0x00];
            let e = try_from(bytes).unwrap_err();
            assert_eq!(Error::RedundantBytes, e);
        }

        // 3 bytes
        {
            let bytes: &[u8] = &[0x82, 0x00, 0x01];
            let e = try_from(bytes).unwrap_err();
            assert_eq!(Error::RedundantBytes, e);

            let bytes: &[u8] = &[0x82, 0x00, 0xff];
            let e = try_from(bytes).unwrap_err();
            assert_eq!(Error::RedundantBytes, e);
        }

        // max
        {
            let mut bytes: [u8; size_of::<usize>() + 2] = [0xff; size_of::<usize>() + 2];
            bytes[0] = 0x80 + (size_of::<usize>() as u8) + 1;
            bytes[1] = 0x00;
            let e = try_from(&bytes).unwrap_err();
            assert_eq!(Error::RedundantBytes, e);
        }
    }

    #[test]
    fn try_from_unterminated() {
        // 2 bytes
        {
            let bytes: &[u8] = &[0x82, 0x01];
            let e = try_from(bytes).unwrap_err();
            assert_eq!(Error::UnTerminatedBytes, e);

            let bytes: &[u8] = &[0x82, 0xff];
            let e = try_from(bytes).unwrap_err();
            assert_eq!(Error::UnTerminatedBytes, e);
        }

        // 3 bytes
        {
            let bytes: &[u8] = &[0x83, 0x01, 0x00];
            let e = try_from(bytes).unwrap_err();
            assert_eq!(Error::UnTerminatedBytes, e);

            let bytes: &[u8] = &[0x83, 0xff, 0xff];
            let e = try_from(bytes).unwrap_err();
            assert_eq!(Error::UnTerminatedBytes, e);
        }

        // max
        {
            let mut bytes: [u8; size_of::<usize>() + 1] = [0xff; size_of::<usize>() + 1];
            bytes[0] = 0x80 + (size_of::<usize>() as u8) + 1;
            let e = try_from(&bytes).unwrap_err();
            assert_eq!(Error::UnTerminatedBytes, e);
        }
    }

    #[test]
    fn to_bytes() {
        let empty: &[u8] = &[];

        // Indefinite
        {
            let bytes = Length::Indefinite.to_bytes();
            let length = try_from(&bytes).unwrap();
            assert_eq!((Length::Indefinite, empty), length);
        }

        // Definite
        for &len in &[0, 1, 0x7f, 0x80, 0xff, 0x0100, 0xffff, std::usize::MAX] {
            let bytes = Length::Definite(len).to_bytes();
            let length = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(len), empty), length);
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
