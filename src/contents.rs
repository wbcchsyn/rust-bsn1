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

//! Provides functions to serialize/deserialize contents octets.

use crate::{Error, StackBuffer};
use core::mem::size_of;
use num::PrimInt;

/// Serializes integer as contents octets.
///
/// Type `T` should be the builtin primitive integer types (e.g., u8, u32, isize, i128, ...)
///
/// This function is common for BER, DER, and CER.
///
/// # Wargnings
///
/// This function assumes that the CPU adopts 2's complement to represent negative value.
pub fn from_integer<T>(val: T) -> impl AsRef<[u8]>
where
    T: PrimInt,
{
    if val < T::zero() {
        from_integer_negative(val)
    } else {
        from_integer_positive(val)
    }
}

fn from_integer_positive<T>(val: T) -> StackBuffer
where
    T: PrimInt,
{
    let mut buffer = StackBuffer::new();

    if val == T::zero() {
        // val == 0.
        unsafe { buffer.push(0x00) };
    } else if val.leading_zeros() == 0 {
        // T is unsigned type and the most significant bit is 1.
        // We must add 0x00 at first.
        let val = val.to_be();

        unsafe {
            buffer.set_len(size_of::<T>() + 1);

            let src = (&val as *const T) as *const u8;

            debug_assert_eq!(0, *buffer.as_ptr());
            let dst = buffer.as_mut_ptr().add(1);

            dst.copy_from_nonoverlapping(src, size_of::<T>());
        }
    } else {
        // The most significant bit is 0.
        // We must skip the first 0x00 bytes to copy.
        let val = val.to_be();
        unsafe {
            let dst = buffer.as_mut_ptr();

            let mut src = (&val as *const T) as *const u8;
            let mut len = size_of::<T>();

            // This loop must finish.
            // (Remember 0 < val.)
            loop {
                if *src == 0 {
                    src = src.add(1);
                    len -= 1;
                } else {
                    break;
                }
            }

            if *src & 0x80 != 0 {
                src = src.sub(1);
                len += 1;
            }

            buffer.set_len(len);
            dst.copy_from_nonoverlapping(src, len);
        }
    }

    buffer
}

/// # Wargnings
///
/// This function assumes that the CPU adopt 2's complement to represent negative value.
fn from_integer_negative<T>(val: T) -> StackBuffer
where
    T: PrimInt,
{
    let mut buffer = StackBuffer::new();
    let val = val.to_be();

    unsafe {
        let mut src = (&val as *const T) as *const u8;
        let mut len = size_of::<T>();

        for _ in 0..size_of::<T>() {
            if *src == 0xff {
                src = src.add(1);
                len -= 1;
            } else {
                break;
            }
        }

        if len == 0 || *src & 0x80 == 0 {
            src = src.sub(1);
            len += 1;
        }

        buffer.set_len(len);

        let dst = buffer.as_mut_ptr();
        dst.copy_from_nonoverlapping(src, len);
    }

    buffer
}

/// Parses `bytes` as a contents of Integer.
///
/// This function is common for BER, DER, and CER.
///
/// # Wargnings
///
/// This function assumes that the CPU adopts 2's complement to represent negative value.
#[inline]
pub fn to_integer(bytes: &[u8]) -> Result<i128, Error> {
    if size_of::<i128>() < bytes.len() {
        Err(Error::OverFlow)
    } else if bytes.is_empty() {
        Err(Error::UnTerminatedBytes)
    } else {
        if 1 < bytes.len() {
            if (bytes[0] == 0) && (bytes[1] & 0x80 == 0x00) {
                return Err(Error::RedundantBytes);
            }
            if (bytes[0] == 0xff) && (bytes[1] & 0x80 == 0x80) {
                return Err(Error::RedundantBytes);
            }
        }

        let init: i128 = if bytes[0] & 0x80 == 0x80 { -1 } else { 0 };
        let ret = bytes.iter().fold(init, |acc, &o| (acc * 256) + (o as i128));
        Ok(ret)
    }
}

/// Serializes boolean as contents octets.
///
/// This function is common for BER, DER, and CER.
#[inline]
pub fn from_bool(val: bool) -> impl AsRef<[u8]> {
    if val {
        [0xff] as [u8; 1]
    } else {
        [0x00] as [u8; 1]
    }
}

/// Parses `bytes` as a BER contents of Bool.
///
/// This function is valid only for the contents of BER, and not applied to the contents of
/// DER nor CER.
#[inline]
pub fn to_bool_ber(bytes: &[u8]) -> Result<bool, Error> {
    if bytes.is_empty() {
        Err(Error::UnTerminatedBytes)
    } else if 1 < bytes.len() {
        Err(Error::InvalidContents)
    } else if bytes[0] == 0x00 {
        Ok(false)
    } else {
        Ok(true)
    }
}

/// Parses `bytes` as a DER contents of Bool.
///
/// This function is valid only for the contents of DER, and not applied to the contents of
/// 'CER' nor 'BER.'
#[inline]
pub fn to_bool_der(bytes: &[u8]) -> Result<bool, Error> {
    if bytes.is_empty() {
        Err(Error::UnTerminatedBytes)
    } else if 1 < bytes.len() {
        Err(Error::InvalidContents)
    } else if bytes[0] == 0x00 {
        Ok(false)
    } else if bytes[0] == 0xff {
        Ok(true)
    } else {
        Err(Error::InvalidContents)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::cast::AsPrimitive;

    #[test]
    fn test_from_integer() {
        // i8
        for i in i8::MIN..=i8::MAX {
            assert_eq!(&[i as u8], from_integer(i).as_ref());
        }

        // u8
        {
            for i in 0..=0x7f {
                assert_eq!(&[i as u8], from_integer(i).as_ref());
            }
            for i in 0x80..=0xff {
                assert_eq!(&[0x00, i as u8], from_integer(i).as_ref());
            }
        }

        // i16
        {
            assert_eq!(&[0x80, 0x00], from_integer(i16::MIN).as_ref());

            for i in i16::MIN..(i8::MIN as i16) {
                let f: u8 = i.unsigned_shr(8).as_();
                let s: u8 = i.as_();
                assert_eq!(&[f, s], from_integer(i).as_ref());
            }

            for i in (i8::MIN as i16)..=(i8::MAX as i16) {
                assert_eq!(&[i as u8], from_integer(i).as_ref());
            }

            for i in 0x80..=i16::MAX {
                let f: u8 = i.unsigned_shr(8).as_();
                let s: u8 = i.as_();
                assert_eq!(&[f, s], from_integer(i).as_ref());
            }

            assert_eq!(&[0x7f, 0xff], from_integer(i16::MAX).as_ref());
        }

        // u16
        {
            assert_eq!(&[0x00], from_integer(u16::MIN).as_ref());

            for i in 0x00..=0x7f_u16 {
                assert_eq!(&[i as u8], from_integer(i).as_ref());
            }

            for i in 0x80..=0xff_u16 {
                assert_eq!(&[0x00, i as u8], from_integer(i).as_ref());
            }

            for i in 0x0100..=0x7fff_u16 {
                let f: u8 = i.unsigned_shr(8).as_();
                let s: u8 = i.as_();
                assert_eq!(&[f, s], from_integer(i).as_ref());
            }

            for i in 0x8000..=u16::MAX {
                let f: u8 = i.unsigned_shr(8).as_();
                let s: u8 = i.as_();
                assert_eq!(&[0x00, f, s], from_integer(i).as_ref());
            }

            assert_eq!(&[0x00, 0xff, 0xff], from_integer(u16::MAX).as_ref());
        }

        // i128::MIN
        {
            let mut expected = [0x00; 16];
            expected[0] = 0x80;
            assert_eq!(&expected, from_integer(i128::MIN).as_ref());
        }

        // i128::MAX
        {
            let mut expected = [0xff; 16];
            expected[0] = 0x7f;
            assert_eq!(&expected, from_integer(i128::MAX).as_ref());
        }

        // 0_u128
        {
            assert_eq!(&[0x00], from_integer(0_u128).as_ref());
        }

        // u128::MAX
        {
            let mut expected = [0xff; 17];
            expected[0] = 0x00;
            assert_eq!(&expected, from_integer(u128::MAX).as_ref());
        }
    }

    #[test]
    fn test_to_integer() {
        // Negative
        {
            // -1
            assert_eq!(-1, to_integer(&[0xff]).unwrap());
            // -0x80
            assert_eq!(-0x80, to_integer(&[0x80]).unwrap());
            // -0x81
            assert_eq!(-0x81, to_integer(&[0xff, 0x7f]).unwrap());
            // -0x0100
            assert_eq!(-0x0100, to_integer(&[0xff, 0x00]).unwrap());
            // -0x0101
            assert_eq!(-0x0101, to_integer(&[0xfe, 0xff]).unwrap());
            // -0x8000
            assert_eq!(-0x8000, to_integer(&[0x80, 0x00]).unwrap());
            // -0x8001
            assert_eq!(-0x8001, to_integer(&[0xff, 0x7f, 0xff]).unwrap());
            // i128::MIN
            {
                let bytes: &mut [u8] = &mut [0x00; size_of::<i128>()];
                bytes[0] = 0x80;
                assert_eq!(std::i128::MIN, to_integer(bytes).unwrap());
            }
        }
        // 0
        assert_eq!(0x00, to_integer(&[0x00]).unwrap());
        // Positive
        {
            // 1
            assert_eq!(1, to_integer(&[0x01]).unwrap());
            // 0x7f
            assert_eq!(0x7f, to_integer(&[0x7f]).unwrap());
            // 0x80
            assert_eq!(0x80, to_integer(&[0x00, 0x80]).unwrap());
            // 0xff
            assert_eq!(0xff, to_integer(&[0x00, 0xff]).unwrap());
            // 0x0100
            assert_eq!(0x0100, to_integer(&[0x01, 0x00]).unwrap());
            // 0x7fff
            assert_eq!(0x7fff, to_integer(&[0x7f, 0xff]).unwrap());
            // 0x8000
            assert_eq!(0x8000, to_integer(&[0x00, 0x80, 0x00]).unwrap());
            // i128::MAX
            {
                let bytes: &mut [u8] = &mut [0xff; size_of::<i128>()];
                bytes[0] = 0x7f;
                assert_eq!(std::i128::MAX, to_integer(bytes).unwrap());
            }
        }
    }
}
