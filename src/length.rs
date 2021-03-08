// Copyright 2021 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause"
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
//
//
// Redistribution and use in source and binary forms, with or without modification, are permitted
// provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice, this
//    list of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
// INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

//! functions and enum about 'Length' octet of 'ASN.1.'

use crate::{Buffer, Error};
use core::mem::size_of;

/// `Length` represents ASN.1 length.
///
/// Note that `Length` represents the byte count of the contents in ASN.1.
/// The total byte size of BER, DER, and CER is greater than that.
/// (BER, DER, and CER are constituted of identifier, length, and contents.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Length {
    /// Represents 'Indefinite' length.
    ///
    /// 'Indefinite' is only for 'BER', and the contents must end with 'EOC' octets.
    Indefinite,
    /// 'Definite' is for 'BER', 'DER', and 'CER', and represents the byte count of the contents.
    Definite(usize),
}

impl Length {
    const LONG_FLAG: u8 = 0x80;
    const MAX_SHORT: u8 = Self::LONG_FLAG - 1;
    const INDEFINITE: u8 = 0x80;
}

/// Tries to parse `bytes` starting with 'length' and returns `Length` .
///
/// This function ignores extra octets at the end of `bytes` .
///
/// # Warnings
///
/// This function may return `Ok(Length::Indefinite)` , however, 'DER' and 'CER' don't allow such
/// value.
/// It does not always mean `bytes` is valid that this function returns `Ok` .
///
/// # Examples
///
/// ```
/// use bsn1::{length_to_bytes, try_length_from, Length};
///
/// let length = Length::Definite(3);
/// let bytes = length_to_bytes(&length);
///
/// let deserialized = try_length_from(bytes.as_ref()).unwrap();
/// assert_eq!(length, deserialized.0);
/// ```
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

        let len = bytes[..followings_count]
            .iter()
            .fold(0, |acc, o| (acc << 8) + (*o as usize));
        let bytes = &bytes[followings_count..];
        Ok((Length::Definite(len), bytes))
    }
}

/// Serializes `length` .
///
/// This function won't allocate heap memory.
///
/// # Examples
///
/// ```
/// use bsn1::{length_to_bytes, try_length_from, Length};
///
/// let length = Length::Definite(3);
/// let bytes = length_to_bytes(&length);
///
/// let deserialized = try_length_from(bytes.as_ref()).unwrap();
/// assert_eq!(length, deserialized.0);
/// ```
pub fn to_bytes(length: &Length) -> impl AsRef<[u8]> {
    let mut buffer = Buffer::new();

    match *length {
        Length::Indefinite => unsafe { buffer.push(Length::INDEFINITE) },
        Length::Definite(mut val) => {
            if val <= Length::MAX_SHORT as usize {
                // Short form
                unsafe { buffer.push(val as u8) };
            } else {
                // Long form
                let len = (8 * size_of::<usize>() - (val.leading_zeros() as usize) + 7) / 8 + 1;
                unsafe { buffer.set_len(len) };
                buffer[0] = Length::LONG_FLAG + (len - 1) as u8;

                for i in (1..len).rev() {
                    debug_assert!(0 < val);
                    buffer[i] = val as u8;
                    val >>= 8;
                }
                debug_assert_eq!(0, val);
            }
        }
    }

    buffer
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
            assert_eq!((Length::Definite(usize::MAX), empty), res);
        }
    }

    #[test]
    fn try_from_extra() {
        let extra: &[u8] = &[1, 2, 3];

        // Indefinite
        {
            let mut bytes = vec![0x80];
            bytes.extend(extra);
            let res = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Indefinite, extra), res);
        }

        // Short form
        {
            let mut bytes = vec![0x00];
            bytes.extend(extra);
            let res = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Definite(0), extra), res);

            let mut bytes = vec![0x7f];
            bytes.extend(extra);
            let res = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Definite(0x7f), extra), res);
        }

        // 2 bytes
        {
            let mut bytes = vec![0x81, 0x80];
            bytes.extend(extra);
            let res = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Definite(0x80), extra), res);

            let mut bytes = vec![0x81, 0xff];
            bytes.extend(extra);
            let res = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Definite(0xff), extra), res);
        }

        // 3 bytes
        {
            let mut bytes = vec![0x82, 0x01, 0x00];
            bytes.extend(extra);
            let res = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Definite(0x0100), extra), res);

            let mut bytes = vec![0x82, 0xff, 0xff];
            bytes.extend(extra);
            let res = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Definite(0xffff), extra), res);
        }

        // max
        {
            let mut bytes: [u8; size_of::<usize>() + 1] = [0xff; size_of::<usize>() + 1];
            bytes[0] = 0x80 + (size_of::<usize>() as u8);
            let mut bytes = Vec::from(&bytes as &[u8]);
            bytes.extend(extra);
            let res = try_from(&bytes).unwrap();
            assert_eq!((Length::Definite(usize::MAX), extra), res);
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
    fn to_bytes_length() {
        let empty: &[u8] = &[];

        // Indefinite
        {
            let bytes = to_bytes(&Length::Indefinite);
            let length = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Indefinite, empty), length);
        }

        // Definite
        for &len in &[0, 1, 0x7f, 0x80, 0xff, 0x0100, 0xffff, usize::MAX] {
            let bytes = to_bytes(&Length::Definite(len));
            let length = try_from(bytes.as_ref()).unwrap();
            assert_eq!((Length::Definite(len), empty), length);
        }
    }
}
