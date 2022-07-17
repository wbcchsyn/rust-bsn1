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

//! Public module `contents` is deprecated.
//! This module is private and will be renamed as `contents` after current `contents` is deleted.

use crate::{Buffer, Error};
use core::borrow::{Borrow, BorrowMut};
use core::mem;
use core::ops::{Deref, DerefMut};
use num::PrimInt;
use std::borrow::ToOwned;
use std::mem::MaybeUninit;

/// `ContentsRef` is a wrapper of [u8] and represents contents octets of ASN.1.
///
/// The user can access to the inner bytes via `Deref` and `DerefMut` implementation.
///
/// This struct is `Unsized`, and user will usually uses a reference to the instance.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentsRef {
    bytes: [u8],
}

impl<'a> From<&'a [u8]> for &'a ContentsRef {
    /// This function is same to `ContentsRef::from_bytes`.
    fn from(bytes: &'a [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl<'a> From<&'a mut [u8]> for &'a mut ContentsRef {
    /// This function is same to `ContentsRef::from_bytes_mut`.
    fn from(bytes: &'a mut [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl ContentsRef {
    /// Creates a reference to `ContentsRef` holding `bytes`.
    ///
    /// This function is same to `<&ContentsRef>::from`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let bytes: &[u8] = &[1, 2, 3];
    /// let contents = ContentsRef::from_bytes(bytes);
    ///
    /// assert_eq!(contents as &[u8], bytes);
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> &Self {
        <&ContentsRef>::from(bytes)
    }

    /// Creates a mutable reference to `ContentsRef` holding `bytes`.
    ///
    /// This function is same to `<&mut ContentsRef>::from`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let bytes: &mut [u8] = &mut [1, 2, 3];
    /// let contents = ContentsRef::from_bytes(bytes);
    ///
    /// assert_eq!(contents as &[u8], &[1, 2, 3]);
    /// ```
    pub fn from_bytes_mut(bytes: &mut [u8]) -> &mut Self {
        <&mut ContentsRef>::from(bytes)
    }

    /// Creates a reference to `ContentsRef` representing `val`.
    ///
    /// The rule of BER bool is different from that of DER and CER, however,
    /// the returned value is valid for all of them.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let true_contents = ContentsRef::from_bool(true);
    ///
    /// assert_eq!(Ok(true), true_contents.to_bool_ber());
    /// assert_eq!(Ok(true), true_contents.to_bool_der());
    ///
    /// let false_contents = ContentsRef::from_bool(false);
    ///
    /// assert_eq!(Ok(false), false_contents.to_bool_ber());
    /// assert_eq!(Ok(false), false_contents.to_bool_der());
    /// ```
    pub fn from_bool(val: bool) -> &'static Self {
        if val {
            Self::from_bytes(&[0xff])
        } else {
            Self::from_bytes(&[0x00])
        }
    }
}

impl AsRef<[u8]> for ContentsRef {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

impl AsMut<[u8]> for ContentsRef {
    fn as_mut(&mut self) -> &mut [u8] {
        self
    }
}

impl Borrow<[u8]> for ContentsRef {
    fn borrow(&self) -> &[u8] {
        self
    }
}

impl BorrowMut<[u8]> for ContentsRef {
    fn borrow_mut(&mut self) -> &mut [u8] {
        self
    }
}

impl Deref for ContentsRef {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}

impl DerefMut for ContentsRef {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bytes
    }
}

impl PartialEq<Contents> for ContentsRef {
    fn eq(&self, other: &Contents) -> bool {
        self == other
    }
}

impl ToOwned for ContentsRef {
    type Owned = Contents;

    fn to_owned(&self) -> Self::Owned {
        Contents::from_bytes(self)
    }
}

impl ContentsRef {
    /// Parses `self` as the ASN.1 contents of integer.
    ///
    /// Type `T` should be the builtin primitive integer types (e.g., u8, i32, isize, i128...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Contents, ContentsRef};
    ///
    /// let contents = Contents::from_integer(17);
    /// assert_eq!(Ok(17_i32), contents.to_integer::<i32>());
    ///
    /// let contents = Contents::from_integer(i32::MAX);
    /// assert!(contents.to_integer::<i16>().is_err());
    ///
    /// let contents = Contents::from_integer(-5);
    /// assert!(contents.to_integer::<u32>().is_err());
    /// ```
    pub fn to_integer<T>(&self) -> Result<T, Error>
    where
        T: PrimInt,
    {
        if self.is_empty() {
            return Err(Error::UnTerminatedBytes);
        }

        if 1 < self.len() {
            if (self[0] == 0) && (self[1] & 0x80 == 0x00) {
                return Err(Error::RedundantBytes);
            }
            if (self[0] == 0xff) && (self[1] & 0x80 == 0x80) {
                return Err(Error::RedundantBytes);
            }
        }

        // If 'T' is Unsigned type and the first octet is 0x00,
        // We can ignore the first byte 0x00.
        let bytes = if self[0] == 0x00 { &self[1..] } else { self };
        if mem::size_of::<T>() < bytes.len() {
            return Err(Error::OverFlow);
        }

        let v = unsafe { self.to_integer_unchecked() };

        if self[0] & 0x80 == 0x00 {
            if v < T::zero() {
                return Err(Error::OverFlow);
            }
        } else {
            if T::zero() <= v {
                return Err(Error::OverFlow);
            }
        }

        Ok(v)
    }

    /// Parses `self` as a contents of ASN.1 integer without any sanitization.
    ///
    /// Type `T` should be the builtin primitive integer type (e.g., u8, i32, isize, u128, ...)
    ///
    /// # Safety
    ///
    /// The behavior is undefined in the following cases.
    ///
    /// - `self` is not formatted as the contents of ASN.1 integer.
    /// - The value is greater than the max value of `T`, or less than the min value of `T`.
    pub unsafe fn to_integer_unchecked<T>(&self) -> T
    where
        T: PrimInt,
    {
        // If 'T' is Unsigned type and the first octet is 0x00,
        // We can ignore the first byte 0x00.
        let bytes = if self[0] == 0x00 { &self[1..] } else { self };
        let filler = if self[0] & 0x80 == 0x00 { 0x00 } else { 0xff };

        let mut be: MaybeUninit<T> = MaybeUninit::uninit();
        be.as_mut_ptr().write_bytes(filler, 1);

        let dst = be.as_mut_ptr() as *mut u8;
        let dst = dst.add(mem::size_of::<T>() - bytes.len());

        dst.copy_from_nonoverlapping(bytes.as_ptr(), bytes.len());

        T::from_be(be.assume_init())
    }

    /// Parses `self` as a contents of BER bool.
    ///
    /// # Warnings
    ///
    /// The rule of BER bool is different from that of DER and CER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let true_contents = ContentsRef::from_bool(true);
    /// assert_eq!(Ok(true), true_contents.to_bool_ber());
    ///
    /// let false_contents = ContentsRef::from_bool(false);
    /// assert_eq!(Ok(false), false_contents.to_bool_ber());
    ///
    /// let bytes = &[0x03];
    /// let ber_contents = ContentsRef::from_bytes(bytes);
    /// assert!(ber_contents.to_bool_ber().is_ok());
    /// assert!(ber_contents.to_bool_der().is_err());
    /// ```
    pub fn to_bool_ber(&self) -> Result<bool, Error> {
        if self.is_empty() {
            Err(Error::UnTerminatedBytes)
        } else if 1 < self.len() {
            Err(Error::InvalidContents)
        } else if self[0] == 0x00 {
            Ok(false)
        } else {
            Ok(true)
        }
    }

    /// Parses `self` as a contents of DER bool.
    ///
    /// # Warnings
    ///
    /// The rule of BER bool is different from that of DER and CER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let true_contents = ContentsRef::from_bool(true);
    /// assert_eq!(Ok(true), true_contents.to_bool_der());
    ///
    /// let false_contents = ContentsRef::from_bool(false);
    /// assert_eq!(Ok(false), false_contents.to_bool_der());
    ///
    /// let bytes = &[0x03];
    /// let ber_contents = ContentsRef::from_bytes(bytes);
    /// assert!(ber_contents.to_bool_ber().is_ok());
    /// assert!(ber_contents.to_bool_der().is_err());
    /// ```
    pub fn to_bool_der(&self) -> Result<bool, Error> {
        if self.is_empty() {
            Err(Error::UnTerminatedBytes)
        } else if 1 < self.len() {
            Err(Error::InvalidContents)
        } else {
            match self[0] {
                0x00 => Ok(false),
                0xff => Ok(true),
                _ => Err(Error::InvalidContents),
            }
        }
    }
}

/// `Contents` owns `ContentsRef` and represents contents octets of ASN.1.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Contents {
    buffer: Buffer,
}

impl From<&[u8]> for Contents {
    /// This function is same to `Contents::from_bytes`.
    fn from(bytes: &[u8]) -> Self {
        Self::from_bytes(bytes)
    }
}

impl From<u8> for Contents {
    /// This function is same to `Contents::from_integer::<u8>`.
    fn from(val: u8) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u16> for Contents {
    /// This function is same to `Contents::from_integer::<u16>`.
    fn from(val: u16) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u32> for Contents {
    /// This function is same to `Contents::from_integer::<u32>`.
    fn from(val: u32) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u64> for Contents {
    /// This function is same to `Contents::from_integer::<u64>`.
    fn from(val: u64) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<u128> for Contents {
    /// This function is same to `Contents::from_integer::<u128>`.
    fn from(val: u128) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<usize> for Contents {
    /// This function is same to `Contents::from_integer::<usize>`.
    fn from(val: usize) -> Self {
        if val == 0 {
            Self::from_zero()
        } else {
            Self::from_positive(val)
        }
    }
}

impl From<i8> for Contents {
    /// This function is same to `Contents::from_integer::<i8>`.
    fn from(val: i8) -> Self {
        Contents::from_integer(val)
    }
}

impl From<i16> for Contents {
    /// This function is same to `Contents::from_integer::<i16>`.
    fn from(val: i16) -> Self {
        Contents::from_integer(val)
    }
}

impl Contents {
    /// Creates a new instance.
    ///
    /// This function is same to `<Contents>::from`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Contents;
    ///
    /// let bytes: &[u8] = &[1, 2, 3];
    /// let contents = Contents::from_bytes(bytes);
    ///
    /// assert_eq!(&contents as &[u8], bytes);
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Serializes boolean and creates a new instance.
    ///
    /// The rule of bool is not common among BER, DER, and CER, however, the returned value is
    /// valid for all of them.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Contents, ContentsRef};
    ///
    /// let true_contents = Contents::from_bool(true);
    /// assert_eq!(Ok(true), true_contents.to_bool_ber());
    /// assert_eq!(Ok(true), true_contents.to_bool_der());
    ///
    /// let false_contents = Contents::from_bool(false);
    /// assert_eq!(Ok(false), false_contents.to_bool_ber());
    /// assert_eq!(Ok(false), false_contents.to_bool_der());
    /// ```
    pub fn from_bool(val: bool) -> Self {
        let mut buffer = Buffer::new();
        if val {
            unsafe { buffer.push(0xff) };
        } else {
            unsafe { buffer.push(0x00) };
        }
        Self { buffer }
    }

    /// Serializes integer and creates a new instance.
    ///
    /// type `T` should be the builtin primitive integer types (e.g., u8, i32, isize, u128, ...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Contents, ContentsRef};
    ///
    /// let contents = Contents::from_integer(35);
    /// assert_eq!(Ok(35), contents.to_integer());
    /// ```
    pub fn from_integer<T>(val: T) -> Self
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
        self
    }
}

impl AsRef<ContentsRef> for Contents {
    fn as_ref(&self) -> &ContentsRef {
        self
    }
}

impl AsMut<[u8]> for Contents {
    fn as_mut(&mut self) -> &mut [u8] {
        self
    }
}

impl AsMut<ContentsRef> for Contents {
    fn as_mut(&mut self) -> &mut ContentsRef {
        self
    }
}

impl Borrow<[u8]> for Contents {
    fn borrow(&self) -> &[u8] {
        self
    }
}

impl Borrow<ContentsRef> for Contents {
    fn borrow(&self) -> &ContentsRef {
        self
    }
}

impl BorrowMut<[u8]> for Contents {
    fn borrow_mut(&mut self) -> &mut [u8] {
        self
    }
}

impl BorrowMut<ContentsRef> for Contents {
    fn borrow_mut(&mut self) -> &mut ContentsRef {
        self
    }
}

impl Deref for Contents {
    type Target = ContentsRef;

    fn deref(&self) -> &Self::Target {
        ContentsRef::from_bytes(self.buffer.as_ref())
    }
}

impl DerefMut for Contents {
    fn deref_mut(&mut self) -> &mut Self::Target {
        ContentsRef::from_bytes_mut(self.buffer.as_mut())
    }
}

impl PartialEq<ContentsRef> for Contents {
    fn eq(&self, other: &ContentsRef) -> bool {
        self == other
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contents_from_i8() {
        for i in i8::MIN..=i8::MAX {
            let contents = Contents::from_integer(i);
            let expected: &[u8] = &[i as u8];

            assert_eq!(&contents as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_u8() {
        for i in 0..0x80 {
            let contents = Contents::from_integer(i as u8);
            let expected: &[u8] = &[i as u8];
            assert_eq!(&contents as &[u8], expected);
        }

        for i in 0x80..=u8::MAX {
            let contents = Contents::from_integer(i as u8);
            let expected: &[u8] = &[0x00, i];
            assert_eq!(&contents as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_i16() {
        for i in i16::MIN..=i16::MAX {
            if (i8::MIN as i16) <= i && i <= (i8::MAX as i16) {
                continue;
            }

            let contents = Contents::from_integer(i);
            let f = i.unsigned_shr(8) as u8;
            let s = i as u8;
            let expected = &[f, s];
            assert_eq!(&contents as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_u16() {
        for i in (i16::MAX as u16 + 1)..=u16::MAX {
            let contents = Contents::from_integer(i);

            let f = i.unsigned_shr(8) as u8;
            let s = i as u8;
            let expected: &[u8] = &[0, f, s];

            assert_eq!(&contents as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_i128() {
        // i128::MIN
        {
            let contents = Contents::from_integer(i128::MIN);

            let mut expected: [u8; 16] = [0x00; 16];
            expected[0] = 0x80;

            assert_eq!(&contents as &[u8], expected);
        }

        // i128::MAX
        {
            let contents = Contents::from_integer(i128::MAX);

            let mut expected: [u8; 16] = [0xff; 16];
            expected[0] = 0x7f;

            assert_eq!(&contents as &[u8], expected);
        }
    }

    #[test]
    fn contents_from_u128() {
        // i128::MAX + 1
        {
            let contents = Contents::from_integer(i128::MAX as u128 + 1);

            let mut expected: [u8; 17] = [0x00; 17];
            expected[1] = 0x80;

            assert_eq!(&contents as &[u8], expected);
        }

        // u128::MAX
        {
            let contents = Contents::from_integer(u128::MAX);

            let mut expected: [u8; 17] = [0xff; 17];
            expected[0] = 0x00;

            assert_eq!(&contents as &[u8], expected);
        }
    }

    #[test]
    fn contents_to_i16_ok() {
        for i in i16::MIN..=i16::MAX {
            let contents = Contents::from_integer(i);
            assert_eq!(Ok(i), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_u16_ok() {
        for i in u16::MIN..=u16::MAX {
            let contents = Contents::from_integer(i);
            assert_eq!(Ok(i), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_i32_ok() {
        // i32::MIN
        {
            const I: i32 = i32::MIN;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i16::MIN - 1
        {
            const I: i32 = i16::MIN as i32 - 1;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i16::MAX + 1
        {
            const I: i32 = i16::MAX as i32 + 1;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i32::MAX
        {
            const I: i32 = i32::MAX;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_u32_ok() {
        // i32::MAX + 1
        {
            const I: u32 = i32::MAX as u32 + 1;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // u32::MAX
        {
            const I: u32 = u32::MAX;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_i128_ok() {
        // i128::MIN
        {
            const I: i128 = i128::MIN;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MIN - 1
        {
            const I: i128 = i64::MIN as i128 - 1;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MIN
        {
            const I: i128 = i64::MIN as i128;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MAX
        {
            const I: i128 = i64::MAX as i128;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i64::MAX + 1
        {
            const I: i128 = i64::MAX as i128 + 1;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
        // i128::MAX
        {
            const I: i128 = i128::MAX;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn contents_to_u128_ok() {
        // i128::MAX + 1
        {
            const I: u128 = i128::MAX as u128 + 1;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }

        // u128::MAX
        {
            const I: u128 = u128::MAX;
            let contents: Contents = Contents::from_integer(I);
            assert_eq!(Ok(I), contents.to_integer());
        }
    }

    #[test]
    fn empty_contents_to_integer() {
        let contents = Contents::from_bytes(&[]);
        assert!(contents.to_integer::<i32>().is_err());
    }

    #[test]
    fn redundant_contents_to_integer() {
        let contents = Contents::from_bytes(&[0x00, 0x00]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from_bytes(&[0x00, 0x7f]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from_bytes(&[0x00, 0x80]);
        assert!(contents.to_integer::<i32>().is_ok());

        let contents = Contents::from_bytes(&[0x00, 0xff]);
        assert!(contents.to_integer::<i32>().is_ok());

        let contents = Contents::from_bytes(&[0xff, 0xff]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from_bytes(&[0xff, 0x80]);
        assert!(contents.to_integer::<i32>().is_err());

        let contents = Contents::from_bytes(&[0xff, 0x7f]);
        assert!(contents.to_integer::<i32>().is_ok());

        let contents = Contents::from_bytes(&[0xff, 0x00]);
        assert!(contents.to_integer::<i32>().is_ok());
    }

    #[test]
    fn overflow_contents_to_integer() {
        // i32::MIN - 1
        {
            let mut bytes = [0xff; 5];
            bytes[1] = 0x7f;

            let contents = ContentsRef::from_bytes(&bytes);
            assert!(contents.to_integer::<i32>().is_err());
            assert!(contents.to_integer::<u32>().is_err());
        }

        // i32::MIN
        {
            let mut bytes = [0x00; 4];
            bytes[0] = 0x80;

            let contents = ContentsRef::from_bytes(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_err());
        }

        // -1
        {
            let bytes = [0xff];

            let contents = ContentsRef::from_bytes(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_err());
        }

        // 0
        {
            let bytes = [0x00];

            let contents = ContentsRef::from_bytes(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_ok());
        }

        // i32::MAX
        {
            let mut bytes = [0xff; 4];
            bytes[0] = 0x7f;

            let contents = ContentsRef::from_bytes(&bytes);
            assert!(contents.to_integer::<i32>().is_ok());
            assert!(contents.to_integer::<u32>().is_ok());
        }

        // i32::MAX + 1
        {
            let mut bytes = [0x00; 5];
            bytes[1] = 0x80;

            let contents = ContentsRef::from_bytes(&bytes);
            assert!(contents.to_integer::<i32>().is_err());
            assert!(contents.to_integer::<u32>().is_ok());
        }
    }

    #[test]
    fn contents_to_i8_unchecked() {
        for i in i8::MIN..=i8::MAX {
            let contents = Contents::from_integer(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u8_unchecked() {
        for i in u8::MIN..=u8::MAX {
            let contents = Contents::from_integer(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_i16_unchecked() {
        for i in i16::MIN..=i16::MAX {
            let contents = Contents::from_integer(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u16_unchecked() {
        for i in u16::MIN..=u16::MAX {
            let contents = Contents::from_integer(i);
            unsafe { assert_eq!(i, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_i32_unchecked() {
        // i32::MIN
        {
            const I: i32 = i32::MIN;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i16::MIN - 1
        {
            const I: i32 = i16::MIN as i32 - 1;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i16::MAX + 1
        {
            const I: i32 = i16::MAX as i32 + 1;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i32::MAX
        {
            const I: i32 = i32::MAX;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u32_unchecked() {
        // i32::MAX + 1
        {
            const I: u32 = i32::MAX as u32 + 1;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // u32::MAX
        {
            const I: u32 = u32::MAX;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_i128_unchecked() {
        // i128::MIN
        {
            const I: i128 = i128::MIN;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i64::MIN - 1
        {
            const I: i128 = i64::MIN as i128 - 1;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i64::MAX + 1
        {
            const I: i128 = i64::MAX as i128 + 1;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // i128::MAX
        {
            const I: i128 = i128::MAX;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_to_u128_unchecked() {
        // i128::MAX + 1
        {
            const I: u128 = i128::MAX as u128 + 1;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }

        // u128::MAX
        {
            const I: u128 = u128::MAX;
            let contents = Contents::from_integer(I);
            unsafe { assert_eq!(I, contents.to_integer_unchecked()) };
        }
    }

    #[test]
    fn contents_ref_from_bool() {
        // True
        {
            let contents = ContentsRef::from_bool(true);
            assert_eq!(&[0xff], contents as &[u8]);
        }

        // false
        {
            let contents = ContentsRef::from_bool(false);
            assert_eq!(&[0x00], contents as &[u8]);
        }
    }

    #[test]
    fn contents_to_bool_ber() {
        // Empty
        {
            let contents = ContentsRef::from_bytes(&[]);
            assert!(contents.to_bool_ber().is_err());
        }

        // 2 or more than 2 bytes
        {
            let contents = ContentsRef::from_bytes(&[1, 2]);
            assert!(contents.to_bool_ber().is_err());

            let contents = ContentsRef::from_bytes(&[1, 2, 3]);
            assert!(contents.to_bool_ber().is_err());
        }

        // false
        {
            let contents = ContentsRef::from_bytes(&[0x00]);
            assert_eq!(Ok(false), contents.to_bool_ber());
        }

        // true
        {
            for i in 1..=u8::MAX {
                let bytes = &[i];
                let contents = ContentsRef::from_bytes(bytes);
                assert_eq!(Ok(true), contents.to_bool_ber());
            }
        }
    }

    #[test]
    fn contents_to_bool_der() {
        // Empty
        {
            let contents = ContentsRef::from_bytes(&[]);
            assert!(contents.to_bool_der().is_err());
        }

        // 2 or more than 2 bytes
        {
            let contents = ContentsRef::from_bytes(&[1, 2]);
            assert!(contents.to_bool_der().is_err());

            let contents = ContentsRef::from_bytes(&[1, 2, 3]);
            assert!(contents.to_bool_der().is_err());
        }

        // false
        {
            let contents = ContentsRef::from_bytes(&[0x00]);
            assert_eq!(Ok(false), contents.to_bool_der());
        }

        // true
        {
            let contents = ContentsRef::from_bytes(&[0xff]);
            assert_eq!(Ok(true), contents.to_bool_der());
        }

        // The others (1 bytes, neither true nor false)
        {
            for i in 1..u8::MAX {
                let bytes = &[i];
                let contents = ContentsRef::from_bytes(bytes);
                assert!(contents.to_bool_der().is_err());
            }
        }
    }

    #[test]
    fn contents_from_bool() {
        // True
        {
            let contents = Contents::from_bool(true);
            assert_eq!(&[0xff], &contents as &[u8]);
        }

        // false
        {
            let contents = Contents::from_bool(false);
            assert_eq!(&[0x00], &contents as &[u8]);
        }
    }
}
