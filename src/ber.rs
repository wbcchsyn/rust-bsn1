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

use crate::{identifier, length, Buffer, ContentsRef, Der, DerRef, Error, IdRef, Length};
use num::PrimInt;
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::mem;
use std::ops::{Deref, DerefMut};

/// `BerRef` is a wrapper of `[u8]` and represents a BER.
///
/// This struct is 'Unsized', and user usually uses a reference to the instance.
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
    /// This function is same to [`BerRef::try_from_bytes`].
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// [`BerRef::try_from_bytes`]: #method.try_from_bytes
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
    /// This function is same to [`BerRef::try_from_mut_bytes`].
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// [`BerRef::try_from_mut_bytes`]: #method.try_from_mut_bytes
    fn try_from(bytes: &'a mut [u8]) -> Result<Self, Self::Error> {
        let ret = <&'a BerRef>::try_from(bytes as &[u8])?;
        let ptr = ret as *const BerRef;
        let ptr = ptr as *mut BerRef;
        unsafe { Ok(&mut *ptr) }
    }
}

impl BerRef {
    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a reference to `BerRef` .
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`<&BerRef>::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// [`<&BerRef>::try_from`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E-for-%26%27a%20BerRef
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // Represents 'True' as Boolean.
    /// let bytes: &[u8] = &[0x01, 0x01, 0xff];
    /// let ber0 = BerRef::try_from_bytes(bytes).unwrap();
    /// assert!(ber0.contents().to_bool_ber().unwrap());
    ///
    /// // The extra octets at the end does not affect to the result.
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
    /// This function is same to [`<&mut BerRef>::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// [`<&mut BerRef>::try_from`]:
    ///     #impl-TryFrom%3C%26%27a%20mut%20%5Bu8%5D%3E-for-%26%27a%20mut%20BerRef
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // Represents '0x04' as an Integer.
    /// let bytes: &mut [u8] = &mut [0x02, 0x01, 0x04];
    /// let ber = BerRef::try_from_mut_bytes(bytes).unwrap();
    ///
    /// // The value is 0x04 at first.
    /// assert_eq!(ber.contents().as_bytes(), &[0x04]);
    ///
    /// ber.mut_contents()[0] = 0x05;
    ///
    /// // The value is updated.
    /// assert_eq!(ber.contents().as_bytes(), &[0x05]);
    /// ```
    pub fn try_from_mut_bytes(bytes: &mut [u8]) -> Result<&mut Self, Error> {
        <&mut Self>::try_from(bytes)
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'BER' or not, use [`TryFrom`]
    /// implementation or [`try_from_bytes`].
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E-for-%26%27a%20BerRef
    /// [`try_from_bytes`]: #method.try_from_bytes
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
    /// If it is not sure whether `bytes` are valid octets as an 'BER' or not, use [`TryFrom`]
    /// implementation or [`try_from_bytes`].
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E-for-%26%27a%20BerRef
    /// [`try_from_bytes`]: #method.try_from_bytes
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

impl Borrow<[u8]> for BerRef {
    fn borrow(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for BerRef {
    type Owned = Ber;

    fn to_owned(&self) -> Self::Owned {
        let buffer = Buffer::from(self.as_bytes());
        Ber { buffer }
    }
}

impl PartialEq<Ber> for BerRef {
    fn eq(&self, other: &Ber) -> bool {
        self == other as &BerRef
    }
}

impl BerRef {
    /// Provides a reference to [`IdRef`] of `self` .
    ///
    /// [`IdRef`]: struct.IdRef.html
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
            let bytes = identifier::shrink_to_fit_unchecked(&self.bytes);
            IdRef::from_bytes_unchecked(bytes)
        }
    }

    /// Provides a mutable reference to [`IdRef`] of `self` .
    ///
    /// [`IdRef`]: struct.IdRef.html
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{BerRef, ClassTag, IdRef, PCTag};
    ///
    /// // Represents '3' as an Integer.
    /// let bytes: &mut [u8] = &mut [0x02, 0x01, 0x03];
    /// let ber = BerRef::try_from_mut_bytes(bytes).unwrap();
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

    /// Returns `Length` of `self`.
    ///
    /// # Warnings
    ///
    /// `Length` stands for 'the length octets of the contents' in BER.
    /// The total byte count is greater than the value.
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

    /// Provides a reference to the 'contents' octets of `self` .
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
        ContentsRef::from_bytes(contents)
    }

    /// Provides a mutable reference to the 'contents' octets of `self` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // Represents 'False' as a Boolean.
    /// let bytes: &mut [u8] = &mut [0x01, 0x01, 0x00];
    /// let ber = BerRef::try_from_mut_bytes(bytes).unwrap();
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

/// `Ber` owns [`BerRef`] and represents a BER.
///
/// The structure of `Ber` is similar to that of `Vec<u8>`.
///
/// User can access to the [`BerRef`] via the [`Deref`] implementation, and to the inner slice via
/// the [`BerRef`].
///
/// [`BerRef`]: struct.BerRef.html
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ber {
    buffer: Buffer,
}

impl From<&DerRef> for Ber {
    fn from(der: &DerRef) -> Self {
        <&BerRef>::from(der).to_owned()
    }
}

impl From<Der> for Ber {
    fn from(der: Der) -> Self {
        Self {
            buffer: crate::der::disassemble_der(der),
        }
    }
}

impl From<&BerRef> for Ber {
    fn from(ber_ref: &BerRef) -> Self {
        ber_ref.to_owned()
    }
}

impl TryFrom<&[u8]> for Ber {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`try_from_bytes`] .
    ///
    /// [`try_from_bytes`]: #method.try_from_bytes
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let ber_ref = <&BerRef>::try_from(bytes)?;
        Ok(ber_ref.to_owned())
    }
}

impl Ber {
    /// Creates a new instance from `id` and `contents` with definite length.
    ///
    /// Note that BER allows both definite and indefinite length, however, this function always
    /// returns definite length value.
    /// (Generally speaking, the performance of definite length is better than that of indefinite
    /// length. Indefinite length is seldom used these days.)
    ///
    /// # Panics
    ///
    /// Panics if the total length exceeds `isize::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = ContentsRef::from_bytes(&[]);
    /// let ber = Ber::new(id, contents);
    ///
    /// assert_eq!(ber.id(), id);
    /// assert!(ber.contents().is_empty());
    /// ```
    pub fn new(id: &IdRef, contents: &ContentsRef) -> Self {
        let der = Der::new(id, contents);
        Self::from(der)
    }

    /// Creates a new instance from `id` and `contents` with indefinite length.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef, Length};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = ContentsRef::from_bytes(&[]);
    /// let ber = Ber::new_indefinite(id, contents);
    ///
    /// assert_eq!(ber.id(), id);
    /// assert_eq!(ber.length().is_indefinite(), true);
    /// assert!(ber.contents().is_empty());
    /// ```
    pub fn new_indefinite(id: &IdRef, contents: &ContentsRef) -> Self {
        let length = Length::Indefinite.to_bytes();
        let total_len = id.len() + length.len() + contents.len();
        let mut buffer = Buffer::with_capacity(total_len);

        unsafe {
            buffer.set_len(total_len);

            let ptr = buffer.as_mut_ptr();
            ptr.copy_from_nonoverlapping(id.as_bytes().as_ptr(), id.len());

            let ptr = ptr.add(id.len());
            ptr.copy_from_nonoverlapping(length.as_ptr(), length.len());

            let ptr = ptr.add(length.len());
            ptr.copy_from_nonoverlapping(contents.as_ptr(), contents.len());
        }

        Self { buffer }
    }

    /// Creates a new instance with definite length from `id` and `contents` of `length` bytes.
    ///
    /// The `contents` of the return value is not initialized.
    /// Use [`mut_contents`] to initialize it.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function accepts
    /// such identifiers.
    /// For example, 'Octet String' must be primitive in DER, but this function will construct a
    /// new instance even if `id` represenets constructed 'Octet String.'
    ///
    /// # Panics
    ///
    /// Panics if the total bytes will exceeds `isize::MAX`.
    ///
    /// [`mut_contents`]: #method.mut_contents
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef, Length};
    ///
    /// let ber = Ber::with_id_length(IdRef::utf8_string(), 36);
    ///
    /// assert_eq!(ber.id(), IdRef::utf8_string());
    /// assert_eq!(ber.length(), Length::Definite(36));
    /// assert_eq!(ber.contents().len(), 36);
    /// ```
    pub fn with_id_length(id: &IdRef, length: usize) -> Self {
        let der = Der::with_id_length(id, length);
        Self::from(der)
    }

    /// Creates a new instance with indefinite length from `id` and `contents` of `length` bytes.
    ///
    /// The `contents` of the return value is not initialized.
    /// Use [`mut_contents`] to initialize it.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function accepts
    /// such identifiers.
    /// For example, 'Octet String' must be primitive in DER, but this function will construct a
    /// new instance even if `id` represenets constructed 'Octet String.'
    ///
    /// # Panics
    ///
    /// Panics if the total bytes will exceeds `isize::MAX`.
    ///
    /// [`mut_contents`]: #method.mut_contents
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef, Length};
    ///
    /// let ber = Ber::with_id_length_indefinite(IdRef::utf8_string(), 36);
    ///
    /// assert_eq!(ber.id(), IdRef::utf8_string());
    /// assert_eq!(ber.length().is_indefinite(), true);
    /// ```
    pub fn with_id_length_indefinite(id: &IdRef, length: usize) -> Self {
        let length_ = Length::Indefinite.to_bytes();
        let total_len = id.len() + length_.len() + length;

        let mut buffer = Buffer::with_capacity(total_len);

        unsafe {
            let dst = buffer.as_mut_ptr();
            dst.copy_from_nonoverlapping(id.as_bytes().as_ptr(), id.len());

            let dst = dst.add(id.len());
            dst.copy_from_nonoverlapping(length_.as_ptr(), length_.len());

            buffer.set_len(total_len);
        }

        Self { buffer }
    }

    /// Parses `bytes` starting with BER octets and builds a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`TryFrom::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// [`TryFrom::try_from`]: #impl-TryFrom%3C%26%5Bu8%5D%3E-for-Ber
    pub fn try_from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::try_from(bytes)
    }

    /// Builds a new instance holding `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'BER' or not, use [`TryFrom`]
    /// implementation or [`try_from_bytes`].
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%5Bu8%5D%3E-for-Ber
    /// [`try_from_bytes`]: #method.try_from_bytes
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a BER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let contents = ContentsRef::from_bytes(&[]);
    /// let ber0 = Ber::new(IdRef::octet_string(), contents);
    /// let ber1 = unsafe { Ber::from_bytes_unchecked(ber0.as_bytes()) };
    /// assert_eq!(ber0, ber1);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Creates a new instance from `id` and `contents` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let id = IdRef::sequence();
    ///
    /// // Build instance using function 'from_id_iterator()'.
    /// let contents: &[Ber] = &[Ber::utf8_string("foo"), Ber::integer(29_i32)];
    /// let ber = Ber::from_id_iterator(id, contents.iter());
    ///
    /// // Build instance using function 'new()'.
    /// let contents: Vec<u8> = contents.iter()
    ///                         .map(|i| Vec::from(i.as_bytes()))
    ///                         .flatten().collect();
    /// let contents = ContentsRef::from_bytes(&contents);
    /// let expected = Ber::new(id, contents);
    ///
    /// assert_eq!(expected, ber);
    /// ```
    pub fn from_id_iterator<I>(id: &IdRef, contents: I) -> Self
    where
        I: Iterator + Clone,
        I::Item: AsRef<[u8]>,
    {
        let der = Der::from_id_iterator(id, contents);
        Self::from(der)
    }

    /// Returns a new instance representing a boolean.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let val = true;
    /// let ber = Ber::boolean(val);
    ///
    /// assert_eq!(IdRef::boolean(), ber.id());
    /// assert_eq!(val, ber.contents().to_bool_ber().unwrap());
    /// ```
    pub fn boolean(val: bool) -> Self {
        Self::from(Der::boolean(val))
    }

    /// Returns a new instance representing an integer.
    ///
    /// Type `T` should be the builtin primitive integer types (e.g., u8, u32, isize, i128, ...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let val = 39;
    /// let ber = Ber::integer(val);
    ///
    /// assert_eq!(IdRef::integer(), ber.id());
    /// assert_eq!(val, ber.contents().to_integer().unwrap());
    /// ```
    pub fn integer<T>(val: T) -> Self
    where
        T: PrimInt,
    {
        Self::from(Der::integer(val))
    }

    /// Returns a new instance representing a utf8_string.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let val = &"foo";
    /// let ber = Ber::utf8_string(val);
    ///
    /// assert_eq!(IdRef::utf8_string(), ber.id());
    /// assert_eq!(val.as_bytes(), ber.contents() as &[u8]);
    /// ```
    pub fn utf8_string(val: &str) -> Self {
        Self::from(Der::utf8_string(val))
    }

    /// Returns a new instance representing an octet_string.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let val = &[1, 2, 3];
    /// let ber = Ber::octet_string(val);
    ///
    /// assert_eq!(IdRef::octet_string(), ber.id());
    /// assert_eq!(val, ber.contents() as &[u8]);
    /// ```
    pub fn octet_string(val: &[u8]) -> Self {
        Self::from(Der::octet_string(val))
    }
}

impl AsRef<[u8]> for Ber {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_bytes()
    }
}

impl Borrow<[u8]> for Ber {
    fn borrow(&self) -> &[u8] {
        self.buffer.borrow()
    }
}

impl Borrow<BerRef> for Ber {
    fn borrow(&self) -> &BerRef {
        self.deref()
    }
}

impl Deref for Ber {
    type Target = BerRef;

    fn deref(&self) -> &Self::Target {
        unsafe { BerRef::from_bytes_unchecked(self.buffer.as_bytes()) }
    }
}

impl DerefMut for Ber {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { BerRef::from_mut_bytes_unchecked(self.buffer.as_mut_bytes()) }
    }
}

impl PartialEq<BerRef> for Ber {
    fn eq(&self, other: &BerRef) -> bool {
        self as &BerRef == other
    }
}

impl Ber {
    /// Consumes `self` , returning `Vec` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = ContentsRef::from_bytes(&[0, 1, 2, 3, 4]);
    ///
    /// let ber = Ber::new(id, contents);
    /// let v = ber.clone().into_vec();
    ///
    /// assert_eq!(ber.as_bytes(), &v);
    /// ```
    pub fn into_vec(self) -> Vec<u8> {
        self.buffer.into_vec()
    }

    /// Force the length of the contents to `new_length`.
    ///
    /// If `new_length` is greater than the current length of the `contents`, this method enlarges
    /// the `contents`. The extended octets are not initialized. Use [`mut_contents`] to initialize.
    ///
    /// If the contents length of `self` forms indefinite, the length octets does not changes;
    /// otherwise the length octets will be updated.
    ///
    /// # Warnings
    ///
    /// `new_length` specifies the length of the contents.
    /// The total length of `self` will be greater then `new_length`.
    ///
    /// # Panics
    ///
    /// Panics if the new total length exceeds `isize::MAX`.
    ///
    /// [`mut_contents`]: #method.mut_contents
    ///
    /// # Examples
    ///
    /// Enlarge indefinite length Ber object.
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef, Length};
    ///
    /// let mut ber = Ber::new_indefinite(IdRef::octet_string(), ContentsRef::from_bytes(&[]));
    ///
    /// assert_eq!(ber.length().is_indefinite(), true);
    /// assert_eq!(ber.contents().as_bytes(), &[]);
    ///
    /// let new_contents: &[u8] = &[0, 1,  2, 3];
    /// ber.set_length(new_contents.len());
    /// ber.mut_contents().as_mut_bytes().clone_from_slice(new_contents);
    ///
    /// assert_eq!(ber.length().is_indefinite(), true);
    /// assert_eq!(ber.contents().as_bytes(), new_contents);
    /// ```
    ///
    /// Enshorten definite length Ber object.
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef, Length};
    ///
    /// let old_contents: &[u8] = &[0, 1, 2, 3, 4];
    /// let mut ber = Ber::new(IdRef::octet_string(), ContentsRef::from_bytes(old_contents));
    ///
    /// assert_eq!(ber.length(), Length::Definite(old_contents.len()));
    /// assert_eq!(ber.contents().as_bytes(), old_contents);
    ///
    /// let new_contents = &old_contents[0..2];
    /// ber.set_length(new_contents.len());
    /// ber.mut_contents().as_mut_bytes().clone_from_slice(new_contents);
    ///
    /// assert_eq!(ber.length(), Length::Definite(new_contents.len()));
    /// assert_eq!(ber.contents().as_bytes(), new_contents);
    /// ```
    pub fn set_length(&mut self, new_length: usize) {
        match self.length() {
            Length::Indefinite => {
                let old_length = self.contents().len();

                let diff = (new_length as isize) - (old_length as isize);

                if 0 < diff {
                    self.buffer.reserve(diff as usize);
                }

                let total_len = self.as_bytes().len() as isize + diff;
                unsafe { self.buffer.set_len(total_len as usize) };
            }
            _ => {
                let this: &mut Der = unsafe { std::mem::transmute(self) };
                this.set_length(new_length);
            }
        };
    }
}

/// Builds a `Ber` instance representing a Constructed BER effectively.
///
/// # Formula
///
/// `constructed_ber!(id: &IdRef [, (id_1, contents_1) [, (id_2, contents_2) [...]]]) => Ber`
///
/// `id_n` and `contents_n` must be bounded on `AsRef<[u8]>` .
///
/// # Examples
///
/// Empty contents.
///
/// ```
/// # #[macro_use] extern crate bsn1;
/// use bsn1::{Ber, ContentsRef, IdRef};
///
/// let id = IdRef::sequence();
/// let contents = ContentsRef::from_bytes(&[]);
/// let expected = Ber::new(id, contents);
/// let ber = constructed_ber!(id);
///
/// assert_eq!(expected, ber);
/// ```
///
/// Sequence of 2 BERs.
///
/// ```
/// # #[macro_use] extern crate bsn1;
/// use bsn1::{Ber, BerRef, Contents, ContentsRef, IdRef};
/// use std::convert::TryFrom;
///
/// let id = IdRef::sequence();
/// let id1 = IdRef::octet_string();
/// let contents1 = ContentsRef::from_bytes(&[1, 2, 3]);
/// let id2 = IdRef::integer();
/// let contents2 = Contents::from_integer(10_i32);
///
/// let ber = constructed_ber!(id, (id1.to_owned(), contents1), (id2, &contents2));
///
/// assert_eq!(id, ber.id());
///
/// let bytes = ber.contents() as &[u8];
/// let ber1 = <&BerRef>::try_from(bytes).unwrap();
/// assert_eq!(id1, ber1.id());
/// assert_eq!(contents1, ber1.contents());
///
/// let bytes = &bytes[ber1.as_bytes().len()..];
/// let ber2 = <&BerRef>::try_from(bytes).unwrap();
/// assert_eq!(id2, ber2.id());
/// assert_eq!(&contents2 as &ContentsRef, ber2.contents());
/// ```
#[macro_export]
macro_rules! constructed_ber {
    ($id:expr $(, ($id_n:expr, $contents_n:expr))*) => {
        Ber::from(constructed_der!($id $(, ($id_n, $contents_n))*))
    };
    ($id:expr $(, ($id_n:expr, $contents_n:expr))*,) => {
        Ber::from(constructed_der!($id $(, ($id_n, $contents_n))*,))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_from_deinite() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = ContentsRef::from_bytes(bytes);
            let ber = Ber::new(id, contents);
            let ber_ref = <&BerRef>::try_from(ber.as_bytes()).unwrap();
            assert_eq!(ber_ref, &ber as &BerRef);
        }
    }

    #[test]
    fn try_from_indefinite() {
        let eoc = {
            let id = IdRef::eoc();
            let contents: &[u8] = &[];
            let contents = ContentsRef::from_bytes(contents);
            Ber::new(id, contents)
        };

        let bers: Vec<Ber> = (0..10)
            .map(|i| {
                let id = IdRef::octet_string();
                let contents: &[u8] = &[i];
                let contents = ContentsRef::from_bytes(contents);
                Ber::new(id, contents)
            })
            .collect();

        for i in 0..10 {
            let id = IdRef::sequence();
            let mut bytes: Vec<u8> = Vec::from(id.as_bytes());

            bytes.extend(Length::Indefinite.to_bytes().iter());

            for ber in bers[0..i].iter() {
                bytes.extend(ber.as_bytes());
            }
            bytes.extend(eoc.as_bytes());

            let ber = <&BerRef>::try_from(&bytes as &[u8]).unwrap();
            assert_eq!(&bytes, ber.as_bytes());
        }
    }

    #[test]
    fn extend_indefinite_ber() {
        let mut ber = Ber::new_indefinite(IdRef::octet_string(), ContentsRef::from_bytes(&[]));

        for i in 0..=256 {
            ber.set_length(i + 1);
            ber.mut_contents()[i] = i as u8;

            assert_eq!(ber.length().is_indefinite(), true);

            let contents = ber.contents();
            assert_eq!(contents.len(), i + 1);
            for j in 0..=i {
                assert_eq!(contents[j], j as u8);
            }
        }

        {
            ber.set_length(65535);
            assert_eq!(ber.length().is_indefinite(), true);

            let contents = ber.contents();
            assert_eq!(contents.len(), 65535);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(65536);
            assert_eq!(ber.length().is_indefinite(), true);

            let contents = ber.contents();
            assert_eq!(contents.len(), 65536);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(256.pow(3) - 1);
            assert_eq!(ber.length().is_indefinite(), true);

            let contents = ber.contents();
            assert_eq!(contents.len(), 256.pow(3) - 1);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(256.pow(3));
            assert_eq!(ber.length().is_indefinite(), true);

            let contents = ber.contents();
            assert_eq!(contents.len(), 256.pow(3));
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }
    }

    #[test]
    fn extend_definite_ber() {
        let mut ber = Ber::new(IdRef::octet_string(), ContentsRef::from_bytes(&[]));

        for i in 0..=256 {
            ber.set_length(i + 1);
            ber.mut_contents()[i] = i as u8;

            assert_eq!(ber.length(), Length::Definite(i + 1));

            let contents = ber.contents();
            assert_eq!(contents.len(), i + 1);
            for j in 0..=i {
                assert_eq!(contents[j], j as u8);
            }
        }

        {
            ber.set_length(65535);
            assert_eq!(ber.length(), Length::Definite(65535));

            let contents = ber.contents();
            assert_eq!(contents.len(), 65535);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(65536);
            assert_eq!(ber.length(), Length::Definite(65536));

            let contents = ber.contents();
            assert_eq!(contents.len(), 65536);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(256.pow(3) - 1);
            assert_eq!(ber.length(), Length::Definite(256.pow(3) - 1));

            let contents = ber.contents();
            assert_eq!(contents.len(), 256.pow(3) - 1);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(256.pow(3));
            assert_eq!(ber.length(), Length::Definite(256.pow(3)));

            let contents = ber.contents();
            assert_eq!(contents.len(), 256.pow(3));
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }
    }

    #[test]
    fn enshorten_indefinite_der() {
        let contents: Vec<u8> = (0..=255).cycle().take(65537).collect();
        let mut ber =
            Ber::new_indefinite(IdRef::octet_string(), ContentsRef::from_bytes(&contents));

        {
            ber.set_length(65536);
            assert_eq!(ber.length().is_indefinite(), true);
            assert_eq!(ber.contents().len(), 65536);

            let contents = ber.contents();
            for i in 0..65536 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(65535);
            assert_eq!(ber.length().is_indefinite(), true);
            assert_eq!(ber.contents().len(), 65535);

            let contents = ber.contents();
            for i in 0..65535 {
                assert_eq!(contents[i], i as u8);
            }
        }

        for i in (0..=256).rev() {
            ber.set_length(i);
            assert_eq!(ber.length().is_indefinite(), true);
            assert_eq!(ber.contents().len(), i);

            let contents = ber.contents();
            for j in 0..i {
                assert_eq!(contents[j], j as u8);
            }
        }
    }

    #[test]
    fn enshorten_definite_der() {
        let contents: Vec<u8> = (0..=255).cycle().take(65536).collect();
        let mut ber = Ber::new(IdRef::octet_string(), ContentsRef::from_bytes(&contents));

        {
            ber.set_length(65536);
            assert_eq!(ber.length(), Length::Definite(65536));
            assert_eq!(ber.contents().len(), 65536);

            let contents = ber.contents();
            for i in 0..65536 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(65535);
            assert_eq!(ber.length(), Length::Definite(65535));
            assert_eq!(ber.contents().len(), 65535);

            let contents = ber.contents();
            for i in 0..65535 {
                assert_eq!(contents[i], i as u8);
            }
        }

        for i in (0..=256).rev() {
            ber.set_length(i);
            assert_eq!(ber.length(), Length::Definite(i));
            assert_eq!(ber.contents().len(), i);

            let contents = ber.contents();
            for j in 0..i {
                assert_eq!(contents[j], j as u8);
            }
        }
    }
}
