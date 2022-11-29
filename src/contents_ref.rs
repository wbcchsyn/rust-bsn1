// Copyright 2021 Shin Yoshida
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

use crate::{Contents, Error};
use core::borrow::{Borrow, BorrowMut};
use core::mem;
use core::ops::{Deref, DerefMut};
use num::PrimInt;
use std::borrow::ToOwned;
use std::mem::MaybeUninit;

/// `ContentsRef` is a wrapper of [u8] and represents 'ASN.1 contents'.
///
/// User can access to the inner slice via [`Deref`] and [`DerefMut`] implementations.
///
/// This struct is `Unsized`, and user will usually use a reference.
///
/// [`Deref`]: #impl-Deref-for-ContentsRef
/// [`DerefMut`]: #impl-DerefMut-for-ContentsRef
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentsRef {
    bytes: [u8],
}

impl<'a> From<&'a [u8]> for &'a ContentsRef {
    /// This function is same to [`ContentsRef::from_bytes`].
    ///
    /// [`ContentsRef::from_bytes`]: #method.from_bytes
    fn from(bytes: &'a [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl<'a> From<&'a mut [u8]> for &'a mut ContentsRef {
    /// This function is same to [`ContentsRef::from_bytes_mut`].
    ///
    /// [`ContentsRef::from_bytes_mut`]: #method.from_bytes_mut
    fn from(bytes: &'a mut [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl From<bool> for &'static ContentsRef {
    /// This function is same to [`ContentsRef::from_bool`].
    ///
    /// [`ContentsRef::from_bool`]: #method.from_bool
    fn from(val: bool) -> Self {
        ContentsRef::from_bool(val)
    }
}

impl ContentsRef {
    /// Creates a reference to `ContentsRef` holding `bytes`.
    ///
    /// This function is same to [`<&ContentsRef>::from`].
    ///
    /// [`<&ContentsRef>::from`]: #impl-From%3C%26%27a%20%5Bu8%5D%3E-for-%26%27a%20ContentsRef
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
    /// This function is same to [`<&mut ContentsRef>::from`].
    ///
    /// [`<&mut ContentsRef>::from`]:
    ///     #impl-From%3C%26%27a%20mut%20%5Bu8%5D%3E-for-%26%27a%20mut%20ContentsRef
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let bytes: &mut [u8] = &mut [1, 2, 3];
    ///
    /// {
    ///     let contents = ContentsRef::from_bytes_mut(bytes);
    ///     assert_eq!(contents as &[u8], &[1, 2, 3]);
    ///
    ///     contents[0] = 10;
    ///     assert_eq!(contents as &[u8], &[10, 2, 3]);
    /// }
    ///
    /// // 'bytes' is updated as well.
    /// assert_eq!(bytes, &[10, 2, 3]);
    /// ```
    pub fn from_bytes_mut(bytes: &mut [u8]) -> &mut Self {
        <&mut ContentsRef>::from(bytes)
    }

    /// Creates a reference to `ContentsRef` representing `val`.
    ///
    /// The rule of 'ASN.1 bool' is slightly different among 'Ber', 'Der', and 'CER', however,
    /// this function is valid for all of them.
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
    /// // Overflow to convert i32::MAX into i16.
    /// let contents = Contents::from_integer(i32::MAX);
    /// assert!(contents.to_integer::<i16>().is_err());
    ///
    /// // Cannot convert a negatibe value into unsigned type.
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

    /// Parses `self` as a contents of ASN.1 integer without any check.
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
    /// // 'BER' regards any octet except for 0x00 as 'True',
    /// // while 'DER' regards octets except for 0x00 and 0xff as error.
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
    /// // 'BER' regards any octet except for 0x00 as 'True',
    /// // while 'DER' regards octets except for 0x00 and 0xff as error.
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
