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
        unsafe { BerRef::from_bytes_unchecked(der.as_ref()) }
    }
}

impl BerRef {
    /// Returns a reference to 'End-of-Contents'.
    pub fn eoc() -> &'static Self {
        const BYTES: [u8; 2] = [0x00, 0x00];
        unsafe { Self::from_bytes_unchecked(&BYTES) }
    }

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a reference to `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores the rule.
    /// For example, number 15 (0x0f) is reserved for now,
    /// but this functions returns `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef};
    ///
    /// // Serializes '8' as an Integer.
    /// let ber = Ber::from(8_u8);
    /// let mut serialized = Vec::from(ber.as_ref() as &[u8]);
    ///
    /// // Deserializes `ber`.
    /// let deserialized = BerRef::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(ber, deserialized);
    ///
    /// // Extra octets at the end does not affect the result.
    /// serialized.push(0x00);
    /// serialized.push(0xff);
    ///
    /// let deserialized = BerRef::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(ber, deserialized);
    /// ```
    pub fn parse<'a>(bytes: &mut &'a [u8]) -> Result<&'a Self, Error> {
        let init_bytes = *bytes;
        let mut stack_depth: isize = 0;

        while {
            stack_depth += Self::do_parse(bytes)? as isize;
            stack_depth > 0
        } {}

        let total_len = init_bytes.len() - bytes.len();
        unsafe { Ok(Self::from_bytes_unchecked(&init_bytes[..total_len])) }
    }

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a mutable reference to
    /// `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores the rule.
    /// For example, number 15 (0x0f) is reserved for now,
    /// but this functions returns `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef};
    ///
    /// // Serialize "Foo" as utf8-string.
    /// let ber = Ber::from("Foo");
    /// let mut serialized = Vec::from(ber.as_ref() as &[u8]);
    ///
    /// // Deserialize.
    /// let deserialized = BerRef::parse_mut(&mut serialized[..]).unwrap();
    /// assert_eq!(ber, deserialized);
    ///
    /// // You can update it because 'deserialized' is a mutable reference.
    /// deserialized.mut_contents()[0] = 'B' as u8;
    /// // Now deserialize represents "Boo", not "Foo".
    ///
    /// // Deserialize again.
    /// let deserialized = BerRef::parse_mut(&mut serialized[..]).unwrap();
    /// assert!(ber != deserialized);
    /// ```
    pub fn parse_mut(bytes: &mut [u8]) -> Result<&mut Self, Error> {
        let mut readable = bytes as &[u8];
        let mut stack_depth: isize = 0;

        while {
            stack_depth += Self::do_parse(&mut readable)? as isize;
            stack_depth > 0
        } {}

        let total_len = bytes.len() - readable.len();
        unsafe { Ok(Self::from_mut_bytes_unchecked(&mut bytes[..total_len])) }
    }

    fn do_parse(readable: &mut &[u8]) -> Result<i8, Error> {
        let mut writeable = std::io::sink();
        let init_bytes = *readable;

        match unsafe { crate::misc::parse_id_length(readable, &mut writeable)? } {
            Length::Definite(contents_len) => {
                if readable.len() < contents_len {
                    Err(Error::UnTerminatedBytes)
                } else {
                    *readable = &readable[contents_len..];

                    let read = &init_bytes[..(init_bytes.len() - readable.len())];
                    if read == Self::eoc().as_ref() {
                        Ok(-1)
                    } else {
                        Ok(0)
                    }
                }
            }
            Length::Indefinite => Ok(1),
        }
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'BER', use [`parse`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let ber = Ber::from(0x34_u8);
    /// let serialized: &[u8] = ber.as_ref();
    /// let deserialized = unsafe { BerRef::from_bytes_unchecked(serialized) };
    ///
    /// assert_eq!(ber, deserialized);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        mem::transmute(bytes)
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as a 'BER', use [`parse_mut`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let ber = Ber::from(0x34_u8);
    /// let mut serialized: Vec<u8> = Vec::from(ber.as_ref() as &[u8]);
    /// let deserialized = unsafe { BerRef::from_mut_bytes_unchecked(&mut serialized[..]) };
    ///
    /// assert_eq!(ber, deserialized);
    ///
    /// *deserialized.mut_contents().as_mut().last_mut().unwrap() += 1;
    /// assert_ne!(ber, deserialized);
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
        unsafe { Ber::from_bytes_unchecked(self.as_ref()) }
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
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let ber = Ber::from(0x05_u8);
    /// let ber: &BerRef = &ber;
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
    /// use bsn1::{Ber, BerRef, ClassTag, IdRef, PCTag};
    ///
    /// let mut ber = Ber::from(0x05_u8);
    /// let ber: &mut BerRef = &mut ber;
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
    /// use bsn1::{Ber, BerRef, Length};
    ///
    /// let ber = Ber::from(false);
    /// let ber: &BerRef = &ber;
    ///
    /// assert_eq!(ber.length(), Length::Definite(ber.contents().len()));
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
    /// use bsn1::{Ber, BerRef};
    ///
    /// let ber = Ber::from(false);
    /// let ber: &BerRef = &ber;
    ///
    /// assert_eq!(ber.contents().to_bool_ber(), Ok(false));
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
    /// use bsn1::{Ber, BerRef, ContentsRef};
    ///
    /// let mut ber = Ber::from(false);
    /// let ber: &mut BerRef = &mut ber;
    ///
    /// assert_eq!(ber.contents().to_bool_ber(), Ok(false));
    ///
    /// let true_contents: &ContentsRef = true.into();
    /// ber.mut_contents().as_mut().copy_from_slice(true_contents.as_ref());
    /// assert_eq!(ber.contents().to_bool_ber(), Ok(true));
    /// ```
    pub fn mut_contents(&mut self) -> &mut ContentsRef {
        unsafe {
            let ret = self.contents();
            let ptr = ret as *const ContentsRef;
            let ptr = ptr as *mut ContentsRef;
            &mut *ptr
        }
    }
}
