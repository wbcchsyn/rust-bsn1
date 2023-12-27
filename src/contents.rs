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

use crate::{Buffer, ContentsRef};
use num::PrimInt;
use std::borrow::Borrow;
use std::mem;
use std::ops::{Deref, DerefMut};

/// `Contents` owns [`ContentsRef`] and represents contents octets of ASN.1.
///
/// The structure of `Contents` is similar to that of `Vec<u8>`.
///
/// The user can access the inner [`ContentsRef`] via the `Deref` and `DerefMut` implementations.
#[derive(Debug, Clone, Eq, Hash)]
pub struct Contents {
    buffer: Buffer,
}

impl From<&'_ ContentsRef> for Contents {
    fn from(value: &'_ ContentsRef) -> Self {
        Self {
            buffer: Buffer::from(value.as_ref()),
        }
    }
}

impl From<&[u8]> for Contents {
    fn from(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }
}

impl<const N: usize> From<&[u8; N]> for Contents {
    fn from(bytes: &[u8; N]) -> Self {
        Self::from(bytes as &[u8])
    }
}

impl<'a> From<&'a str> for Contents {
    fn from(value: &'a str) -> Self {
        Self::from(value.as_bytes())
    }
}

impl From<Vec<u8>> for Contents {
    fn from(value: Vec<u8>) -> Self {
        Self {
            buffer: Buffer::from(value),
        }
    }
}

impl From<String> for Contents {
    fn from(value: String) -> Self {
        Self {
            buffer: Buffer::from(value.into_bytes()),
        }
    }
}

impl From<u8> for Contents {
    fn from(val: u8) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u16> for Contents {
    fn from(val: u16) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u32> for Contents {
    fn from(val: u32) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u64> for Contents {
    fn from(val: u64) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u128> for Contents {
    fn from(val: u128) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<usize> for Contents {
    fn from(val: usize) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<i8> for Contents {
    fn from(val: i8) -> Self {
        Contents::from_integer(val)
    }
}

impl From<i16> for Contents {
    fn from(val: i16) -> Self {
        Contents::from_integer(val)
    }
}

impl From<i32> for Contents {
    fn from(val: i32) -> Self {
        Contents::from_integer(val)
    }
}

impl From<i64> for Contents {
    fn from(val: i64) -> Self {
        Contents::from_integer(val)
    }
}

impl From<i128> for Contents {
    fn from(val: i128) -> Self {
        Contents::from_integer(val)
    }
}

impl From<isize> for Contents {
    fn from(val: isize) -> Self {
        Contents::from_integer(val)
    }
}

impl From<bool> for Contents {
    /// The encoding rule of boolean is different between BER and DER.
    /// The return value is valid both as BER and DER.
    fn from(val: bool) -> Self {
        let buffer = if val {
            Buffer::from(&[0xff])
        } else {
            Buffer::from(&[0x00])
        };
        Self { buffer }
    }
}

impl Contents {
    /// Serializes integer and creates a new instance.
    fn from_integer<T>(val: T) -> Self
    where
        T: PrimInt,
    {
        if val < T::zero() {
            Self::from_negative(val)
        } else if val == T::zero() {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }

    fn from_zero() -> Self {
        let mut buffer = Buffer::new();
        unsafe { buffer.push(0x00) };
        Self { buffer }
    }

    fn from_positive<T>(val: T) -> Self
    where
        T: PrimInt,
    {
        debug_assert!(T::zero() < val);

        let vals = [T::zero(), val.to_be()];
        let (src, len) = unsafe {
            let mut src = (&vals[1] as *const T) as *const u8;
            let mut len = mem::size_of::<T>();

            // This loop must be finished because 0 < val.
            while *src == 0 {
                src = src.add(1);
                len -= 1;
            }
            if *src & 0x80 == 0x80 {
                src = src.sub(1);
                len += 1;
            }

            (src, len)
        };

        let mut buffer = Buffer::with_capacity(len);
        let dst = buffer.as_mut_ptr();
        unsafe {
            buffer.set_len(len);
            dst.copy_from_nonoverlapping(src, len);
        }

        Self { buffer }
    }

    fn from_negative<T>(val: T) -> Self
    where
        T: PrimInt,
    {
        debug_assert!(val < T::zero());

        let val = val.to_be();

        let (src, len) = unsafe {
            let mut src = (&val as *const T) as *const u8;
            let mut len = mem::size_of::<T>();

            while 1 < len && *src == 0xff {
                src = src.add(1);
                len -= 1;
            }

            if *src & 0x80 == 0 {
                src = src.sub(1);
                len += 1;
            }

            (src, len)
        };

        let mut buffer = Buffer::with_capacity(len);
        let dst = buffer.as_mut_ptr();

        unsafe {
            buffer.set_len(len);
            dst.copy_from_nonoverlapping(src, len);
        }

        Self { buffer }
    }
}

impl AsRef<[u8]> for Contents {
    fn as_ref(&self) -> &[u8] {
        self.deref().as_ref()
    }
}

impl AsRef<ContentsRef> for Contents {
    fn as_ref(&self) -> &ContentsRef {
        self
    }
}

impl AsMut<[u8]> for Contents {
    fn as_mut(&mut self) -> &mut [u8] {
        self.deref_mut().as_mut()
    }
}

impl AsMut<ContentsRef> for Contents {
    fn as_mut(&mut self) -> &mut ContentsRef {
        self
    }
}

impl Borrow<ContentsRef> for Contents {
    fn borrow(&self) -> &ContentsRef {
        self
    }
}

impl Deref for Contents {
    type Target = ContentsRef;

    fn deref(&self) -> &Self::Target {
        <&ContentsRef>::from(self.buffer.as_bytes())
    }
}

impl DerefMut for Contents {
    fn deref_mut(&mut self) -> &mut Self::Target {
        <&mut ContentsRef>::from(self.buffer.as_mut_bytes())
    }
}

impl<T> PartialEq<T> for Contents
where
    T: Borrow<ContentsRef>,
{
    fn eq(&self, other: &T) -> bool {
        self.deref() == other.borrow()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contents_from_i8() {
        for i in i8::MIN..=i8::MAX {
            let contents = Contents::from(i);
            let expected: &[u8] = &[i as u8];

            assert_eq!(contents.as_ref() as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_u8() {
        for i in 0..0x80 {
            let contents = Contents::from(i as u8);
            let expected: &[u8] = &[i as u8];
            assert_eq!(contents.as_ref() as &[u8], expected);
        }

        for i in 0x80..=u8::MAX {
            let contents = Contents::from(i as u8);
            let expected: &[u8] = &[0x00, i];
            assert_eq!(contents.as_ref() as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_i16() {
        for i in i16::MIN..=i16::MAX {
            if (i8::MIN as i16) <= i && i <= (i8::MAX as i16) {
                continue;
            }

            let contents = Contents::from(i);
            let f = i.unsigned_shr(8) as u8;
            let s = i as u8;
            let expected = &[f, s];
            assert_eq!(contents.as_ref() as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_u16() {
        for i in (i16::MAX as u16 + 1)..=u16::MAX {
            let contents = Contents::from(i);

            let f = i.unsigned_shr(8) as u8;
            let s = i as u8;
            let expected: &[u8] = &[0, f, s];

            assert_eq!(contents.as_ref() as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_i128() {
        // i128::MIN
        {
            let contents = Contents::from(i128::MIN);

            let mut expected: [u8; 16] = [0x00; 16];
            expected[0] = 0x80;

            assert_eq!(contents.as_ref() as &[u8], expected);
        }

        // i128::MAX
        {
            let contents = Contents::from(i128::MAX);

            let mut expected: [u8; 16] = [0xff; 16];
            expected[0] = 0x7f;

            assert_eq!(contents.as_ref() as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_u128() {
        // i128::MAX + 1
        {
            let contents = Contents::from(i128::MAX as u128 + 1);

            let mut expected: [u8; 17] = [0x00; 17];
            expected[1] = 0x80;

            assert_eq!(contents.as_ref() as &[u8], expected);
        }

        // u128::MAX
        {
            let contents = Contents::from(u128::MAX);

            let mut expected: [u8; 17] = [0xff; 17];
            expected[0] = 0x00;

            assert_eq!(contents.as_ref() as &[u8], expected);
        }
    }

    #[test]
    fn contents_to_i16_ok() {
        for i in i16::MIN..=i16::MAX {
            let contents = Contents::from(i);
            assert_eq!(Ok(i), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_u16_ok() {
        for i in u16::MIN..=u16::MAX {
            let contents = Contents::from(i);
            assert_eq!(Ok(i), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_i32_ok() {
        // i32::MIN
        {
            const I: i32 = i32::MIN;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i16::MIN - 1
        {
            const I: i32 = i16::MIN as i32 - 1;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i16::MAX + 1
        {
            const I: i32 = i16::MAX as i32 + 1;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i32::MAX
        {
            const I: i32 = i32::MAX;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_u32_ok() {
        // i32::MAX + 1
        {
            const I: u32 = i32::MAX as u32 + 1;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // u32::MAX
        {
            const I: u32 = u32::MAX;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_i128_ok() {
        // i128::MIN
        {
            const I: i128 = i128::MIN;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MIN - 1
        {
            const I: i128 = i64::MIN as i128 - 1;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MIN
        {
            const I: i128 = i64::MIN as i128;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MAX
        {
            const I: i128 = i64::MAX as i128;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MAX + 1
        {
            const I: i128 = i64::MAX as i128 + 1;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i128::MAX
        {
            const I: i128 = i128::MAX;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_u128_ok() {
        // i128::MAX + 1
        {
            const I: u128 = i128::MAX as u128 + 1;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }

        // u128::MAX
        {
            const I: u128 = u128::MAX;
            let contents: Contents = Contents::from(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn empty_contents_to_integer() {
        let contents = Contents::from(&[]);
        assert!(contents.to_integer::<i32>().is_err());
    }

    #[test]
    fn redundant_contents_to_integer() {
        let contents = Contents::from(&[0x00, 0x00]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from(&[0x00, 0x7f]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from(&[0x00, 0x80]);
        assert!(contents.to_integer::<i32>().is_ok());

        let contents = Contents::from(&[0x00, 0xff]);
        assert!(contents.to_integer::<i32>().is_ok());

        let contents = Contents::from(&[0xff, 0xff]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from(&[0xff, 0x80]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from(&[0xff, 0x7f]);
        assert!(contents.to_integer::<i32>().is_ok());

        let contents = Contents::from(&[0xff, 0x00]);
        assert!(contents.to_integer::<i32>().is_ok());
    }

    #[test]
    fn overflow_contents_to_integer() {
        // i32::MIN - 1
        {
            let mut bytes = [0xff; 5];
            bytes[1] = 0x7f;

            let contents = <&ContentsRef>::from(&bytes);
            assert!(contents.to_integer::<i32>().is_err());
            assert!(contents.to_integer::<u32>().is_err());
        }

        // i32::MIN
        {
            let mut bytes = [0x00; 4];
            bytes[0] = 0x80;

            let contents = <&ContentsRef>::from(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_err());
        }

        // -1
        {
            let bytes = [0xff];

            let contents = <&ContentsRef>::from(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_err());
        }

        // 0
        {
            let bytes = [0x00];

            let contents = <&ContentsRef>::from(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_ok());
        }

        // i32::MAX
        {
            let mut bytes = [0xff; 4];
            bytes[0] = 0x7f;

            let contents = <&ContentsRef>::from(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_ok());
        }

        // i32::MAX + 1
        {
            let mut bytes = [0x00; 5];
            bytes[1] = 0x80;

            let contents = <&ContentsRef>::from(&bytes);
            assert!(contents.to_integer::<i32>().is_err());
            assert!(contents.to_integer::<u32>().is_ok());
        }
    }

    #[test]
    fn contents_to_i8_unchecked() {
        for i in i8::MIN..=i8::MAX {
            let contents = Contents::from(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u8_unchecked() {
        for i in u8::MIN..=u8::MAX {
            let contents = Contents::from(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_i16_unchecked() {
        for i in i16::MIN..=i16::MAX {
            let contents = Contents::from(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u16_unchecked() {
        for i in u16::MIN..=u16::MAX {
            let contents = Contents::from(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_i32_unchecked() {
        // i32::MIN
        {
            const I: i32 = i32::MIN;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i16::MIN - 1
        {
            const I: i32 = i16::MIN as i32 - 1;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i16::MAX + 1
        {
            const I: i32 = i16::MAX as i32 + 1;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i32::MAX
        {
            const I: i32 = i32::MAX;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u32_unchecked() {
        // i32::MAX + 1
        {
            const I: u32 = i32::MAX as u32 + 1;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // u32::MAX
        {
            const I: u32 = u32::MAX;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_i128_unchecked() {
        // i128::MIN
        {
            const I: i128 = i128::MIN;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i64::MIN - 1
        {
            const I: i128 = i64::MIN as i128 - 1;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i64::MAX + 1
        {
            const I: i128 = i64::MAX as i128 + 1;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i128::MAX
        {
            const I: i128 = i128::MAX;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u128_unchecked() {
        // i128::MAX + 1
        {
            const I: u128 = i128::MAX as u128 + 1;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // u128::MAX
        {
            const I: u128 = u128::MAX;
            let contents = Contents::from(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_bool_ber() {
        // Empty
        {
            let contents = <&ContentsRef>::from(&[]);
            assert!(contents.to_bool_ber().is_err());
        }

        // 2 or more than 2 bytes
        {
            let contents = <&ContentsRef>::from(&[1, 2]);
            assert!(contents.to_bool_ber().is_err());

            let contents = <&ContentsRef>::from(&[1, 2, 3]);
            assert!(contents.to_bool_ber().is_err());
        }

        // false
        {
            let contents = <&ContentsRef>::from(&[0x00]);
            assert_eq!(Ok(false), contents.to_bool_ber());
        }

        // true
        {
            for i in 1..=u8::MAX {
                let bytes = &[i];
                let contents = <&ContentsRef>::from(bytes);
                assert_eq!(Ok(true), contents.to_bool_ber());
            }
        }
    }

    #[test]
    fn contents_to_bool_der() {
        // Empty
        {
            let contents = <&ContentsRef>::from(&[]);
            assert!(contents.to_bool_der().is_err());
        }

        // 2 or more than 2 bytes
        {
            let contents = <&ContentsRef>::from(&[1, 2]);
            assert!(contents.to_bool_der().is_err());

            let contents = <&ContentsRef>::from(&[1, 2, 3]);
            assert!(contents.to_bool_der().is_err());
        }

        // false
        {
            let contents = <&ContentsRef>::from(&[0x00]);
            assert_eq!(Ok(false), contents.to_bool_der());
        }

        // true
        {
            let contents = <&ContentsRef>::from(&[0xff]);
            assert_eq!(Ok(true), contents.to_bool_der());
        }

        // The others (1 bytes, neither true nor false)
        {
            for i in 1..u8::MAX {
                let bytes = &[i];
                let contents = <&ContentsRef>::from(bytes);
                assert!(contents.to_bool_der().is_err());
            }
        }
    }

    #[test]
    fn from_bool() {
        // True
        {
            let contents = Contents::from(true);
            assert_eq!(&[0xff], contents.as_ref() as &[u8]);
        }

        // false
        {
            let contents = Contents::from(false);
            assert_eq!(&[0x00], contents.as_ref() as &[u8]);
        }
    }
}
