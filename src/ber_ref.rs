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

use crate::{identifier_ref, length, Ber, ContentsRef, DerRef, Error, IdRef, Length};
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::mem;

/// `BerRef` is a wrapper of `[u8]` and represents a BER.
///
/// This struct is 'Unsized' and the user will usually use a reference to the instance.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct BerRef {
    bytes: [u8],
}

impl<'a> From<&'a DerRef> for &'a BerRef {
    fn from(der: &'a DerRef) -> Self {
        unsafe { BerRef::from_bytes_unchecked(der.as_bytes()) }
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a BerRef {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a reference to `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`BerRef::try_from_bytes`].
    ///
    /// [Read more](std::convert::TryFrom::try_from)
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        let id = <&IdRef>::try_from(bytes)?;
        let parsing = &bytes[id.len()..];

        match length::try_from(parsing) {
            Err(e) => Err(e),
            Ok((Length::Definite(len), parsing)) => {
                let total_len = bytes.len() - parsing.len() + len;

                if bytes.len() < total_len {
                    Err(Error::UnTerminatedBytes)
                } else {
                    unsafe { Ok(BerRef::from_bytes_unchecked(&bytes[..total_len])) }
                }
            }
            Ok((Length::Indefinite, mut parsing)) => {
                while {
                    let element = Self::try_from(parsing)?;
                    let len = element.as_bytes().len();
                    parsing = &parsing[len..];

                    if element.id() != IdRef::eoc() {
                        true
                    } else if element.contents().is_empty() {
                        false
                    } else {
                        return Err(Error::BadEoc);
                    }
                } {}
                let total_len = bytes.len() - parsing.len();
                unsafe { Ok(BerRef::from_bytes_unchecked(&bytes[..total_len])) }
            }
        }
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut BerRef {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a mutable reference to
    /// `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`BerRef::parse_mut`].
    ///
    /// [Read more](std::convert::TryFrom::try_from)
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    fn try_from(bytes: &'a mut [u8]) -> Result<Self, Self::Error> {
        let ret = <&'a BerRef>::try_from(bytes as &[u8])?;
        let ptr = ret as *const BerRef;
        let ptr = ptr as *mut BerRef;
        unsafe { Ok(&mut *ptr) }
    }
}

impl BerRef {
    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a reference to `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`TryFrom::try_from`].
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// [`TryFrom::try_from`]: #method.try_from
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // Represents 'True' as a Boolean.
    /// let bytes: &[u8] = &[0x01, 0x01, 0xff];
    /// let ber0 = BerRef::try_from_bytes(bytes).unwrap();
    /// assert!(ber0.contents().to_bool_ber().unwrap());
    ///
    /// // The extra octets at the end do not affect the result.
    /// let bytes: &[u8] = &[0x01, 0x01, 0xff, 0x00];
    /// let ber1 = BerRef::try_from_bytes(bytes).unwrap();
    /// assert_eq!(ber0, ber1);
    /// ```
    pub fn try_from_bytes(bytes: &[u8]) -> Result<&Self, Error> {
        <&Self>::try_from(bytes)
    }

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a mutable reference to
    /// `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`TryFrom::try_from`].
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// [`TryFrom::try_from`]: #method.try_from-1
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // Represents '0x04' as an Integer.
    /// let bytes: &mut [u8] = &mut [0x02, 0x01, 0x04];
    /// let ber = BerRef::parse_mut(bytes).unwrap();
    ///
    /// // The value is 0x04 at first.
    /// assert_eq!(ber.contents().as_bytes(), &[0x04]);
    ///
    /// ber.mut_contents()[0] = 0x05;
    ///
    /// // The value is updated.
    /// assert_eq!(ber.contents().as_bytes(), &[0x05]);
    /// ```
    pub fn parse_mut(bytes: &mut [u8]) -> Result<&mut Self, Error> {
        <&mut Self>::try_from(bytes)
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'BER', use [`TryFrom`]
    /// implementation or [`try_from_bytes`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`TryFrom`]: #method.try_from
    /// [`try_from_bytes`]: Self::try_from_bytes
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{BerRef, IdRef};
    ///
    /// // Represents '0x34' as an Integer.
    /// let bytes: &[u8] = &[0x02, 0x01, 0x34];
    /// let ber = unsafe { BerRef::from_bytes_unchecked(bytes) };
    ///
    /// assert_eq!(ber.id(), IdRef::integer());
    /// assert_eq!(ber.contents().to_integer::<i32>().unwrap(), 0x34);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        mem::transmute(bytes)
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as a 'BER', use [`TryFrom`]
    /// implementation or [`parse_mut`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`TryFrom`]: #method.try_from-1
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{BerRef, IdRef};
    ///
    /// // Represents '0x34' as an Integer.
    /// let bytes: &[u8] = &[0x02, 0x01, 0x34];
    /// let ber = unsafe { BerRef::from_bytes_unchecked(bytes) };
    ///
    /// assert_eq!(ber.id(), IdRef::integer());
    /// assert_eq!(ber.contents().to_integer::<i32>().unwrap(), 0x34);
    /// ```
    pub unsafe fn from_mut_bytes_unchecked(bytes: &mut [u8]) -> &mut Self {
        mem::transmute(bytes)
    }
}

impl AsRef<[u8]> for BerRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for BerRef {
    type Owned = Ber;

    fn to_owned(&self) -> Self::Owned {
        unsafe { Ber::from_bytes_unchecked(self.as_bytes()) }
    }
}

impl<T> PartialEq<T> for BerRef
where
    T: Borrow<BerRef>,
{
    fn eq(&self, other: &T) -> bool {
        self == other.borrow()
    }
}

impl BerRef {
    /// Provides a reference to the [`IdRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{BerRef, IdRef};
    ///
    /// // Represents '3' as an Integer.
    /// let bytes: &[u8] = &[0x02, 0x01, 0x03];
    /// let ber = BerRef::try_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(ber.id(), IdRef::integer());
    /// ```
    pub fn id(&self) -> &IdRef {
        unsafe {
            let bytes = identifier_ref::shrink_to_fit_unchecked(&self.bytes);
            IdRef::from_bytes_unchecked(bytes)
        }
    }

    /// Provides a mutable reference to the [`IdRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{BerRef, ClassTag, IdRef, PCTag};
    ///
    /// // Represents '3' as an Integer.
    /// let bytes: &mut [u8] = &mut [0x02, 0x01, 0x03];
    /// let ber = BerRef::parse_mut(bytes).unwrap();
    ///
    /// assert_eq!(ber.id(), IdRef::integer());
    ///
    /// assert_eq!(ber.id().class(), ClassTag::Universal);
    /// ber.mut_id().set_class(ClassTag::Private);
    /// assert_eq!(ber.id().class(), ClassTag::Private);
    ///
    /// assert_eq!(ber.id().pc(), PCTag::Primitive);
    /// ber.mut_id().set_pc(PCTag::Constructed);
    /// assert_eq!(ber.id().pc(), PCTag::Constructed);
    /// ```
    pub fn mut_id(&mut self) -> &mut IdRef {
        unsafe {
            let ret = self.id();
            let ptr = ret as *const IdRef;
            let ptr = ptr as *mut IdRef;
            &mut *ptr
        }
    }

    /// Returns the [`Length`] of `self`.
    ///
    /// # Warnings
    ///
    /// `Length` stands for 'the length octets' in BER.
    /// It implies the byte count of `contents` or `indefinite`.
    /// The total byte count is greater than the value even if it is `definite`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{BerRef, Length};
    ///
    /// // Represents 'False' as a Boolean.
    /// let bytes: &[u8] = &[0x01, 0x01, 0x00];
    /// let ber = BerRef::try_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(ber.length(), Length::Definite(1));
    /// ```
    pub fn length(&self) -> Length {
        let id_len = self.id().len();
        let bytes = &self.bytes[id_len..];
        unsafe { length::from_bytes_starts_with_unchecked(bytes).0 }
    }

    /// Provides a reference to the [`ContentsRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // Represents 'False' as a Boolean.
    /// let bytes: &[u8] = &[0x01, 0x01, 0x00];
    /// let ber = BerRef::try_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(ber.contents().to_bool_ber().unwrap(), false);
    /// ```
    pub fn contents(&self) -> &ContentsRef {
        let id_len = self.id().len();
        let bytes = &self.bytes[id_len..];
        let contents = unsafe { length::from_bytes_starts_with_unchecked(bytes).1 };
        <&ContentsRef>::from(contents)
    }

    /// Provides a mutable reference to the [`ContentsRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // Represents 'False' as a Boolean.
    /// let bytes: &mut [u8] = &mut [0x01, 0x01, 0x00];
    /// let ber = BerRef::parse_mut(bytes).unwrap();
    ///
    /// assert_eq!(ber.contents().to_bool_ber().unwrap(), false);
    ///
    /// ber.mut_contents()[0] = 0xff;
    /// assert_eq!(ber.contents().to_bool_ber().unwrap(), true);
    /// ```
    pub fn mut_contents(&mut self) -> &mut ContentsRef {
        unsafe {
            let ret = self.contents();
            let ptr = ret as *const ContentsRef;
            let ptr = ptr as *mut ContentsRef;
            &mut *ptr
        }
    }

    /// Provides a reference to the inner slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // This octets represents '3' as an integer.
    /// let bytes = vec![0x02, 0x01, 0x03];
    ///
    /// let ber = unsafe { BerRef::from_bytes_unchecked(&bytes) };
    /// assert_eq!(&bytes, ber.as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}
