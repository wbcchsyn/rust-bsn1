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

use crate::{length, ContentsRef, Der, Error, IdRef, Length};
use std::borrow::Borrow;
use std::convert::TryFrom;

/// `DerRef` is a wrapper of `[u8]` and represents DER.
///
/// This struct is 'Unsized', and the user will usually use a reference.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct DerRef {
    bytes: [u8],
}

impl<'a> TryFrom<&'a [u8]> for &'a DerRef {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a reference to `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`DerRef::parse`].
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`Read more`](std::convert::TryFrom::try_from)
    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        let id = <&IdRef>::try_from(bytes)?;
        let parsing = &bytes[id.len()..];

        let (len, parsing) = match length::parse_(parsing) {
            Err(Error::OverFlow) => return Err(Error::UnTerminatedBytes),
            Err(e) => return Err(e),
            Ok((Length::Indefinite, _)) => return Err(Error::IndefiniteLength),
            Ok((Length::Definite(len), parsing)) => (len, parsing),
        };

        let total_len = bytes.len() - parsing.len() + len;
        if bytes.len() < total_len {
            Err(Error::UnTerminatedBytes)
        } else {
            unsafe { Ok(DerRef::from_bytes_unchecked(&bytes[..total_len])) }
        }
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut DerRef {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a mutable reference to
    /// `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`DerRef::parse_mut`].
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`Read more`](std::convert::TryFrom::try_from)
    fn try_from(bytes: &'a mut [u8]) -> Result<Self, Self::Error> {
        let ret = DerRef::parse(bytes)?;
        let ptr = ret as *const DerRef;
        let ptr = ptr as *mut DerRef;
        unsafe { Ok(&mut *ptr) }
    }
}

impl DerRef {
    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a reference to `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`TryFrom::try_from`].
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`TryFrom::try_from`]: #method.try_from
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::DerRef;
    ///
    /// // Represents '8' as Integer.
    /// let bytes0: &[u8] = &[0x02, 0x01, 0x08];
    /// let der0 = DerRef::parse(bytes0).unwrap();
    ///
    /// // The result is not changed even if extra octets are added to the end.
    /// let bytes1: &[u8] = &[0x02, 0x01, 0x08, 0x00, 0xff];
    /// let der1 = DerRef::parse(bytes1).unwrap();
    ///
    /// assert_eq!(der0, der1);
    /// ```
    pub fn parse(bytes: &[u8]) -> Result<&Self, Error> {
        <&Self>::try_from(bytes)
    }

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a mutable reference to
    /// `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`TryFrom::try_from`].
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`TryFrom::try_from`]: #method.try_from-1
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{DerRef, IdRef};
    ///
    /// // Represents '8' as Integer.
    /// let bytes: &mut [u8] = &mut [0x02, 0x01, 0x08];
    /// let der = DerRef::parse_mut(bytes).unwrap();
    ///
    /// // The value is 0x08 at first.
    /// assert_eq!(der.contents().as_bytes(), &[0x08]);
    ///
    /// der.mut_contents()[0] = 0x09;
    ///
    /// // The value is updated.
    /// assert_eq!(der.contents().as_bytes(), &[0x09]);
    /// ```
    pub fn parse_mut(bytes: &mut [u8]) -> Result<&mut Self, Error> {
        <&mut Self>::try_from(bytes)
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as a 'DER', use [`TryFrom`]
    /// implementation or [`parse`] instead.
    ///
    /// [`TryFrom`]: #method.try_from
    /// [`parse`]: Self::parse
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::DerRef;
    ///
    /// let bytes: &[u8] = &[0x02, 0x01, 0x08];  // Represents '8' as Integer.
    /// let _der: &DerRef = unsafe { DerRef::from_bytes_unchecked(bytes) };
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        let ptr = bytes as *const [u8];
        let ptr = ptr as *const Self;
        &*ptr
    }

    /// Provides a mutable reference from `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as a 'DER', use [`TryFrom`]
    /// implementation or [`parse_mut`] instead.
    ///
    /// [`TryFrom`]: #method.try_from-1
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::DerRef;
    ///
    /// // Represents '8' as Integer.
    /// let bytes: &mut [u8] = &mut [0x02, 0x01, 0x08];
    /// let der = unsafe { DerRef::from_mut_bytes_unchecked(bytes) };
    ///
    /// // The value is 0x08 at first.
    /// assert_eq!(der.contents().as_bytes(), &[0x08]);
    ///
    /// der.mut_contents()[0] = 0x09;
    ///
    /// // The value is updated.
    /// assert_eq!(der.contents().as_bytes(), &[0x09]);
    /// ```
    pub unsafe fn from_mut_bytes_unchecked(bytes: &mut [u8]) -> &mut Self {
        std::mem::transmute(bytes)
    }
}

impl AsRef<[u8]> for DerRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl Borrow<[u8]> for DerRef {
    fn borrow(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for DerRef {
    type Owned = Der;

    fn to_owned(&self) -> Self::Owned {
        unsafe { Der::from_bytes_unchecked(self.as_bytes()) }
    }
}

impl PartialEq<Der> for DerRef {
    fn eq(&self, other: &Der) -> bool {
        self == other as &DerRef
    }
}

impl DerRef {
    /// Returns a reference to the `IdRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{DerRef, IdRef};
    ///
    /// let bytes: &[u8] = &[0x02, 0x01, 0x04];  // Represents '4' as Integer.
    /// let der = DerRef::parse(bytes).unwrap();
    ///
    /// assert_eq!(IdRef::integer(), der.id());
    /// ```
    pub fn id(&self) -> &IdRef {
        unsafe {
            let bytes = crate::identifier_ref::shrink_to_fit_unchecked(&self.bytes);
            IdRef::from_bytes_unchecked(bytes)
        }
    }

    /// Returns a mutable reference to the `IdRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, DerRef, IdRef, PCTag};
    ///
    /// // Represents '4' as Integer.
    /// let bytes: &mut [u8] = &mut [0x02, 0x01, 0x04];
    /// let der = DerRef::parse_mut(bytes).unwrap();
    ///
    /// assert_eq!(der.id().class(), ClassTag::Universal);
    /// der.mut_id().set_class(ClassTag::Private);
    /// assert_eq!(der.id().class(), ClassTag::Private);
    ///
    /// assert_eq!(der.id().pc(), PCTag::Primitive);
    /// der.mut_id().set_pc(PCTag::Constructed);
    /// assert_eq!(der.id().pc(), PCTag::Constructed);
    /// ```
    pub fn mut_id(&mut self) -> &mut IdRef {
        let ret = self.id();
        let ptr = ret as *const IdRef;
        let ptr = ptr as *mut IdRef;
        unsafe { &mut *ptr }
    }

    /// Returns `Length` of `self`.
    ///
    /// Note that DER does not allow indefinite Length.
    /// The return value is always `Length::Definite`.
    ///
    /// # Warnings
    ///
    /// `Length` stands for the length octets in DER: i.e. the length of the contents.
    /// The total byte count of the DER is greater than the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{DerRef, Length};
    ///
    /// let bytes: &[u8] = &[0x04, 0x02, 0x00, 0xff];  // Represents '[0x00, 0xff]' as Octet String
    /// let der = DerRef::parse(bytes).unwrap();
    ///
    /// assert_eq!(Length::Definite(2), der.length());
    /// ```
    pub fn length(&self) -> Length {
        let id_len = self.id().len();
        let bytes = &self.bytes[id_len..];
        unsafe { length::from_bytes_starts_with_unchecked(bytes).0 }
    }

    /// Returns a reference to the contents octets of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ContentsRef, DerRef};
    ///
    /// let bytes: &[u8] = &[0x04, 0x02, 0x00, 0xff];  // Represents '[0x00, 0xff]' as Octet String
    /// let der = DerRef::parse(bytes).unwrap();
    /// let contents = <&ContentsRef>::from(&bytes[2..]);
    ///
    /// assert_eq!(contents, der.contents());
    /// ```
    pub fn contents(&self) -> &ContentsRef {
        let id_len = self.id().len();
        let bytes = &self.bytes[id_len..];
        let bytes = unsafe { length::from_bytes_starts_with_unchecked(bytes).1 };
        <&ContentsRef>::from(bytes)
    }

    /// Returns a mutable reference to the contents octets of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ContentsRef, DerRef};
    ///
    /// // Represents '[0x00, 0xff]' as Octet String
    /// let bytes: &mut [u8] = &mut [0x04, 0x02, 0x00, 0xff];
    /// let der = DerRef::parse_mut(bytes).unwrap();
    ///
    /// assert_eq!(der.contents().as_bytes(), &[0x00, 0xff]);
    /// der.mut_contents().as_mut_bytes().copy_from_slice(&[0x01, 0x02]);
    /// assert_eq!(der.contents().as_bytes(), &[0x01, 0x02]);
    /// ```
    pub fn mut_contents(&mut self) -> &mut ContentsRef {
        let ret = self.contents();
        let ptr = ret as *const ContentsRef;
        let ptr = ptr as *mut ContentsRef;
        unsafe { &mut *ptr }
    }

    /// Provides a reference to the inner slice.
    ///
    /// # Example
    ///
    /// ```
    /// use bsn1::DerRef;
    ///
    /// // This octets represents `3` as integer.
    /// let bytes = vec![0x02, 0x01, 0x03];
    ///
    /// let der = DerRef::parse(&bytes).unwrap();
    /// assert_eq!(&bytes, der.as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}
