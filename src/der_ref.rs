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

/// `DerRef` is a wrapper of `[u8]` and represents DER.
///
/// This struct is 'Unsized', and the user will usually use a reference.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct DerRef {
    bytes: [u8],
}

impl DerRef {
    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a reference to `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// // Serializes '8' as Integer.
    /// let der = Der::from(8_i32);
    /// let mut serialized = Vec::from(der.as_ref() as &[u8]);
    ///
    /// // Deserialize `der`.
    /// let deserialized = DerRef::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(der, deserialized);
    ///
    /// // The result is not changed even if extra octets are added to the end.
    /// serialized.push(0xff);
    /// serialized.push(0x00);
    ///
    /// let deserialized = DerRef::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(der, deserialized);
    /// ```
    pub fn parse<'a>(bytes: &mut &'a [u8]) -> Result<&'a Self, Error> {
        let init_bytes = *bytes;
        Self::do_parse(bytes)?;

        let total_len = init_bytes.len() - bytes.len();
        let read = &init_bytes[..total_len];
        unsafe { Ok(Self::from_bytes_unchecked(read)) }
    }

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a mutable reference to
    /// `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// // Serialize "Foo" as utf8-string.
    /// let der = Der::from("Foo");
    /// let mut serialized = Vec::from(der.as_ref() as &[u8]);
    ///
    /// // Deserialize.
    /// let deserialized = DerRef::parse_mut(&mut serialized[..]).unwrap();
    /// assert_eq!(der, deserialized);
    ///
    /// // You can update it because 'deserialized' is a mutable reference.
    /// deserialized.mut_contents()[0] = 'B' as u8;
    ///
    /// // Now `deserialized` represents "Boo", not "Foo".
    ///
    /// // Deserialize again.
    /// let deserialized = DerRef::parse_mut(&mut serialized[..]).unwrap();
    /// assert!(der != deserialized);
    /// ```
    pub fn parse_mut(bytes: &mut [u8]) -> Result<&mut Self, Error> {
        let mut readable = bytes as &[u8];
        Self::do_parse(&mut readable)?;

        let len = bytes.len() - readable.len();
        unsafe { Ok(Self::from_mut_bytes_unchecked(&mut bytes[..len])) }
    }

    fn do_parse(readable: &mut &[u8]) -> Result<(), Error> {
        let mut writeable = std::io::sink();

        let length = match unsafe { crate::misc::parse_id_length(readable, &mut writeable)? } {
            Length::Indefinite => return Err(Error::IndefiniteLength),
            Length::Definite(length) => length,
        };

        if readable.len() < length {
            Err(Error::UnTerminatedBytes)
        } else {
            *readable = &readable[length..];
            Ok(())
        }
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as a 'DER', use [`parse`] instead.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// let der = Der::from(8_i32);
    /// let serialized: Vec<u8> = Vec::from(der.as_ref() as &[u8]);
    /// let deserialized = unsafe { DerRef::from_bytes_unchecked(&serialized[..]) };
    ///
    /// assert_eq!(der, deserialized);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        std::mem::transmute(bytes)
    }

    /// Provides a mutable reference from `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as a 'DER', use [`parse_mut`] instead.
    ///
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// let der = Der::from(8_i32);
    /// let mut serialized: Vec<u8> = Vec::from(der.as_ref() as &[u8]);
    /// let deserialized = unsafe { DerRef::from_mut_bytes_unchecked(&mut serialized[..]) };
    ///
    /// assert_eq!(der, deserialized);
    ///
    /// deserialized.mut_contents()[0] += 1;
    ///
    /// assert_ne!(der, deserialized);
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

impl ToOwned for DerRef {
    type Owned = Der;

    fn to_owned(&self) -> Self::Owned {
        unsafe { Der::from_bytes_unchecked(self.as_ref()) }
    }
}

impl<T> PartialEq<T> for DerRef
where
    T: Borrow<DerRef>,
{
    fn eq(&self, other: &T) -> bool {
        self == other.borrow()
    }
}

impl DerRef {
    /// Returns a reference to the `IdRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, IdRef};
    ///
    /// let der = Der::from(4_i32);
    /// let der: &DerRef = der.as_ref();
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
    /// use bsn1::{ClassTag, Der, DerRef, IdRef, PCTag};
    ///
    /// let mut der = Der::from(4_i32);
    /// let der: &mut DerRef = der.as_mut();
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
    /// `Length` stands for the length octets in DER: i.e. the length of the 'contents octets'.
    /// The total byte count of the DER is greater than the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, Length};
    ///
    /// let der = Der::from("Foo");
    /// let der: &DerRef = der.as_ref();
    ///
    /// assert_eq!(Length::Definite("Foo".len()), der.length());
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
    /// use bsn1::{ContentsRef, Der, DerRef};
    ///
    /// let der = Der::from("Foo");
    /// let der: &DerRef = der.as_ref();
    ///
    /// assert_eq!(der.contents().as_ref(), "Foo".as_bytes());
    /// ```
    pub fn contents(&self) -> &ContentsRef {
        let id_len = self.id().len();
        let bytes = &self.bytes[id_len..];
        let bytes = unsafe { length::from_bytes_starts_with_unchecked(bytes).1 };
        <&ContentsRef>::from(bytes)
    }

    /// Returns a mutable reference to the 'contents octets' of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ContentsRef, Der, DerRef};
    ///
    /// let mut der = Der::from("Foo");
    /// let der: &mut DerRef = der.as_mut();
    ///
    /// assert_eq!(der.contents().as_ref(), "Foo".as_bytes());
    ///
    /// der.mut_contents()[0] = 'B' as u8;
    /// assert_eq!(der.contents().as_ref(), "Boo".as_bytes());
    /// ```
    pub fn mut_contents(&mut self) -> &mut ContentsRef {
        let ret = self.contents();
        let ptr = ret as *const ContentsRef;
        let ptr = ptr as *mut ContentsRef;
        unsafe { &mut *ptr }
    }
}
