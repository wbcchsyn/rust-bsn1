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

use crate::{identifier, length, Buffer, ContentsRef, Der, DerRef, Error, IdRef, Length};
use core::convert::TryFrom;
use core::mem;
use core::ops::Deref;
use num::PrimInt;
use std::borrow::Borrow;

/// `BerRef` is a wrapper of `[u8]` and represents a BER.
///
/// This struct is 'Unsized', and user usually uses a reference to the instance.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct BerRef {
    bytes: [u8],
}

impl<'a> From<&'a DerRef> for &'a BerRef {
    #[inline]
    fn from(der: &'a DerRef) -> Self {
        unsafe { BerRef::from_bytes_unchecked(der.as_ref()) }
    }
}

impl<'a> TryFrom<&'a [u8]> for &'a BerRef {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a reference to `BerRef` .
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        let id = <&IdRef>::try_from(bytes)?;
        let parsing = &bytes[id.as_ref().len()..];

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
                    let len = element.as_ref().len();
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

impl BerRef {
    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a reference to `BerRef` .
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`<&BerRef>::try_from`] .
    ///
    /// [`<&BerRef>::try_from`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    pub fn from_bytes(bytes: &[u8]) -> Result<&Self, Error> {
        <&Self>::try_from(bytes)
    }

    /// Provides a reference from `bytes` without any sanitization.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'BER' or not, use [`TryFrom`]
    /// implementation or [`from_bytes`].
    ///
    /// The difference from [`from_bytes_starts_with_unchecked`] is that
    /// [`from_bytes_starts_with_unchecked`] checks the 'LENGTH' octets and excludes extra
    /// octet(s) at the end if any while this method does not check at all (i.e.
    /// [`from_bytes_starts_with_unchecked`] allows extra octets at the end.)
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`from_bytes_starts_with_unchecked`]: #method.from_bytes_starts_with_unchecked
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    /// [`from_bytes`]: #method.from_bytes
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let ber = Ber::new(id, &[]);
    ///
    /// let bytes: &[u8] = ber.as_ref();
    /// let deserialized = unsafe { BerRef::from_bytes_unchecked(bytes) };
    /// assert_eq!(ber.as_ref() as &BerRef, deserialized);
    /// ```
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        mem::transmute(bytes)
    }

    /// Provides a reference from `bytes` that starts with a BER octets.
    ///
    /// `bytes` may include some extra octet(s) at the end.
    ///
    /// If it is not sure whether `bytes` starts with BER octets or not, use [`TryFrom`]
    /// implementation or [`from_bytes`].
    ///
    /// The difference from [`from_bytes_unchecked`] is that this function checks the 'LENGTH'
    /// octets and excludes extra octet(s) at the end if any, while [`from_bytes_unchecked`]
    /// does not check at all.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` does not start with BER octets.
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    /// [`from_bytes_unchecked`]: #method.from_bytes_unchecked
    /// [`from_bytes`]: #method.from_bytes
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let ber = Ber::new(id, &[]);
    /// let mut bytes = Vec::from(ber.as_ref() as &[u8]);
    /// bytes.extend(&[1, 2, 3]);
    ///
    /// let deserialized = unsafe { BerRef::from_bytes_starts_with_unchecked(bytes.as_ref()) };
    /// assert_eq!(ber.as_ref() as &BerRef, deserialized);
    /// ```
    #[inline]
    pub unsafe fn from_bytes_starts_with_unchecked(bytes: &[u8]) -> &Self {
        let id = identifier::shrink_to_fit_unchecked(bytes);
        let parsing = &bytes[id.len()..];

        let total_len = match length::from_bytes_starts_with_unchecked(parsing) {
            (Length::Definite(len), parsing) => bytes.len() - parsing.len() + len,
            (Length::Indefinite, parsing) => {
                let mut total_len = bytes.len() - parsing.len();
                let mut parsing = parsing;
                while {
                    let element = Self::from_bytes_starts_with_unchecked(parsing);
                    total_len += element.as_ref().len();
                    parsing = &parsing[element.as_ref().len()..];

                    element.id() != IdRef::eoc()
                } {}
                total_len
            }
        };

        let bytes = &bytes[..total_len];
        Self::from_bytes_unchecked(bytes)
    }
}

impl AsRef<[u8]> for BerRef {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl Borrow<[u8]> for BerRef {
    #[inline]
    fn borrow(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for BerRef {
    type Owned = Ber;

    fn to_owned(&self) -> Self::Owned {
        let buffer = Buffer::from(self.as_ref());
        Ber { buffer }
    }
}

impl PartialEq<Ber> for BerRef {
    #[inline]
    fn eq(&self, other: &Ber) -> bool {
        self == other.as_ref() as &BerRef
    }
}

impl BerRef {
    /// Provides a reference to `IdRef` of `self` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = &[1, 2, 3];
    ///
    /// // 'Ber' implements 'Deref<Target=BerRef>.'
    /// let ber = Ber::new(id, contents);
    /// assert_eq!(id, ber.id());
    /// ```
    #[inline]
    pub fn id(&self) -> &IdRef {
        unsafe {
            let bytes = identifier::shrink_to_fit_unchecked(&self.bytes);
            IdRef::from_bytes_unchecked(bytes)
        }
    }

    /// Returns `Length` of `self` .
    ///
    /// # Warnings
    ///
    /// `Length` stands for 'the length octets of the contents' in BER.
    /// The total bytes is greater than the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef, Length};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = &[1, 2, 3];
    ///
    /// // 'Ber' implements 'Deref<Target=BerRef>.'
    /// let ber = Ber::new(id, contents);
    /// assert_eq!(Length::Definite(contents.len()), ber.length());
    /// ```
    #[inline]
    pub fn length(&self) -> Length {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        unsafe { length::from_bytes_starts_with_unchecked(bytes).0 }
    }

    /// Provides a reference to the 'contents' octets of `self` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = &[1, 2, 3];
    ///
    /// // 'Ber' implements 'Deref<Target=BerRef>.'
    /// let ber = Ber::new(id, contents);
    /// assert_eq!(contents, ber.contents());
    /// ```
    #[inline]
    pub fn contents(&self) -> &[u8] {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        unsafe { length::from_bytes_starts_with_unchecked(bytes).1 }
    }

    /// Provides a reference to the inner slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::BerRef;
    ///
    /// // This octets represents '3' as integer.
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
/// [`BerRef`]: struct.BerRef.html
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ber {
    buffer: Buffer,
}

impl From<&DerRef> for Ber {
    #[inline]
    fn from(der: &DerRef) -> Self {
        <&BerRef>::from(der).to_owned()
    }
}

impl From<Der> for Ber {
    #[inline]
    fn from(der: Der) -> Self {
        Self {
            buffer: crate::der::disassemble_der(der),
        }
    }
}

impl From<&BerRef> for Ber {
    #[inline]
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
    /// This function is same to [`from_bytes`] .
    ///
    /// [`from_bytes`]: #method.from_bytes
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let ber_ref = <&BerRef>::try_from(bytes)?;
        Ok(ber_ref.to_owned())
    }
}

impl Ber {
    /// Creates a new instance from `id` and `contents` with definite length.
    ///
    /// Note that BER allows both definite and indefinite length, however, the length of the return
    /// value is always definite.
    /// (Generally speaking, the performance of definite length is better than that of indefinite
    /// length. Indefinite length is seldom used these days.)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = ContentsRef::from_bytes(&[]);
    /// let _ber = Ber::new(id, contents);
    /// ```
    pub fn new(id: &IdRef, contents: &ContentsRef) -> Self {
        let der = Der::new(id, contents);
        Self::from(der)
    }

    /// Parses `bytes` starting with BER octets and builds a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`TryFrom::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for BER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String BER.
    ///
    /// [`TryFrom::try_from`]: #impl-TryFrom%3C%26%27_%20%5Bu8%5D%3E
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::try_from(bytes)
    }

    /// Builds a new instance holding `bytes` without any sanitization.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'BER' or not, use [`TryFrom`]
    /// implementation or [`from_bytes`].
    ///
    /// The difference from [`from_bytes_starts_with_unchecked`] is that
    /// [`from_bytes_starts_with_unchecked`] checks the 'LENGTH' octets and excludes extra
    /// octet(s) at the end if any while this method does not check at all (i.e.
    /// [`from_bytes_starts_with_unchecked`] allows extra octets at the end.)
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27_%20%5Bu8%5D%3E
    /// [`from_bytes`]: #method.from_bytes
    /// [`from_bytes_starts_with_unchecked`]: #method.from_bytes_starts_with_unchecked
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a BER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let ber0 = Ber::new(IdRef::octet_string(), &[]);
    /// let ber1 = unsafe { Ber::from_bytes_unchecked(ber0.as_ref()) };
    /// assert_eq!(ber0, ber1);
    /// ```
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Builds a new instance from `bytes` that starts with 'BER' octets.
    ///
    /// `bytes` may include some extra octet(s) at the end.
    ///
    /// If it is not sure whether `bytes` starts with DER octets or not, use [`TryFrom`]
    /// implementation or [`from_bytes`] .
    ///
    /// The difference from [`from_bytes_unchecked`] is that this function checks the 'LENGTH'
    /// octets and excludes extra octet(s) at the end if any, while [`from_bytes_unchecked`]
    /// does not check at all.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` does not start with 'ASN.1 BER' octets.
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27_%20%5Bu8%5D%3E
    /// [`from_bytes_unchecked`]: #method.from_bytes_unchecked
    /// [`from_bytes`]: #method.from_bytes
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let ber0 = Ber::new(IdRef::octet_string(), &[]);
    /// let mut bytes = Vec::from(ber0.as_ref() as &[u8]);
    /// bytes.extend(&[1, 2, 3]);
    ///
    /// let ber1 = unsafe { Ber::from_bytes_starts_with_unchecked(bytes.as_ref()) };
    /// assert_eq!(ber0, ber1);
    /// ```
    #[inline]
    pub unsafe fn from_bytes_starts_with_unchecked(bytes: &[u8]) -> Self {
        let id = identifier::shrink_to_fit_unchecked(bytes);
        let parsing = &bytes[id.len()..];

        let (len, parsing) = match length::from_bytes_starts_with_unchecked(parsing) {
            (Length::Definite(len), parsing) => (len, parsing),
            _ => panic!("{}", Error::IndefiniteLength),
        };

        let total_len = bytes.len() - parsing.len() + len;
        let bytes = &bytes[..total_len];
        Self::from_bytes_unchecked(bytes)
    }

    /// Creates a new instance from `id` and `contents` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let id = IdRef::sequence();
    ///
    /// // Build instance using function 'from_id_iterator()'.
    /// let contents: &[Ber] = &[Ber::utf8_string("foo"), Ber::integer(29)];
    /// let ber = Ber::from_id_iterator(id, contents.iter());
    ///
    /// // Build instance using function 'new()'.
    /// let contents: Vec<u8> = contents.iter()
    ///                         .map(|i| Vec::from(i.as_ref() as &[u8]))
    ///                         .flatten().collect();
    /// let expected = Ber::new(id, &contents);
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

    /// Returns a new instance representing boolean.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{contents, Ber, IdRef};
    ///
    /// let val = true;
    /// let ber = Ber::boolean(val);
    ///
    /// assert_eq!(IdRef::boolean(), ber.id());
    /// assert_eq!(val, contents::to_bool_ber(ber.contents()).unwrap());
    /// ```
    pub fn boolean(val: bool) -> Self {
        Self::from(Der::boolean(val))
    }

    /// Returns a new instance representing integer.
    ///
    /// Type `T` should be the builtin primitive integer types (e.g., u8, u32, isize, i128, ...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{contents, Ber, IdRef};
    ///
    /// let val = 39;
    /// let ber = Ber::integer(val);
    ///
    /// assert_eq!(IdRef::integer(), ber.id());
    /// assert_eq!(val, contents::to_integer(ber.contents()).unwrap());
    /// ```
    pub fn integer<T>(val: T) -> Self
    where
        T: PrimInt,
    {
        Self::from(Der::integer(val))
    }

    /// Returns a new instance representing utf8_string.
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
    /// assert_eq!(val.as_bytes(), ber.contents());
    /// ```
    pub fn utf8_string(val: &str) -> Self {
        Self::from(Der::utf8_string(val))
    }

    /// Returns a new instance representing octet_string.
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
    /// assert_eq!(val, ber.contents());
    /// ```
    pub fn octet_string(val: &[u8]) -> Self {
        Self::from(Der::octet_string(val))
    }
}

impl AsRef<[u8]> for Ber {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

impl AsRef<BerRef> for Ber {
    #[inline]
    fn as_ref(&self) -> &BerRef {
        self.deref()
    }
}

impl Borrow<[u8]> for Ber {
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.buffer.borrow()
    }
}

impl Borrow<BerRef> for Ber {
    #[inline]
    fn borrow(&self) -> &BerRef {
        self.deref()
    }
}

impl Deref for Ber {
    type Target = BerRef;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { BerRef::from_bytes_unchecked(self.buffer.as_ref()) }
    }
}

impl PartialEq<BerRef> for Ber {
    #[inline]
    fn eq(&self, other: &BerRef) -> bool {
        self.as_ref() as &BerRef == other
    }
}

impl Ber {
    /// Consumes `self` , returning `Vec` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents: &[u8] = &[0, 1, 2, 3, 4];
    ///
    /// let ber = Ber::new(id, contents);
    /// let v = ber.clone().into_vec();
    ///
    /// assert_eq!(ber.as_ref() as &[u8], v.as_ref() as &[u8]);
    /// ```
    pub fn into_vec(self) -> Vec<u8> {
        self.buffer.into_vec()
    }
}

/// Builds a `Ber` instance representing Constructed BER effectively.
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
/// use bsn1::{Ber, IdRef};
///
/// let id = IdRef::sequence();
/// let expected = Ber::new(id, &[]);
/// let ber = constructed_ber!(id);
///
/// assert_eq!(expected, ber);
/// ```
///
/// Sequence of 2 BERs.
///
/// ```
/// # #[macro_use] extern crate bsn1;
/// use bsn1::{contents, Ber, BerRef, IdRef};
/// use std::convert::TryFrom;
///
/// let id = IdRef::sequence();
/// let id1 = IdRef::octet_string();
/// let contents1: [u8; 3] = [1, 2, 3];
/// let id2 = IdRef::integer();
/// let contents2 = contents::from_integer(10);
///
/// let ber = constructed_ber!(id, (id1.to_owned(), contents1), (id2, &contents2));
///
/// assert_eq!(id, ber.id());
///
/// let bytes = ber.contents();
/// let ber1 = <&BerRef>::try_from(bytes).unwrap();
/// assert_eq!(id1, ber1.id());
/// assert_eq!(contents1, ber1.contents());
///
/// let bytes = &bytes[ber1.as_ref().len()..];
/// let ber2 = <&BerRef>::try_from(bytes).unwrap();
/// assert_eq!(id2, ber2.id());
/// assert_eq!(contents2.as_ref(), ber2.contents());
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
    fn from_bytes_starts_with_unchecked_definite() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        let extras: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = ContentsRef::from_bytes(bytes);
            let ber = Ber::new(id, contents);

            for &extra in extras {
                let mut bytes = Vec::from(ber.as_ref() as &[u8]);
                bytes.extend(extra);

                let ber_ref = unsafe { BerRef::from_bytes_starts_with_unchecked(bytes.as_ref()) };
                assert_eq!(ber_ref, &ber);
            }
        }
    }

    #[test]
    fn from_bytes_starts_with_unchecked_infinite() {
        let eoc = {
            let id = IdRef::eoc();
            let contents = ContentsRef::from_bytes(&[]);
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
            let mut bytes: Vec<u8> = Vec::from(id.as_ref() as &[u8]);

            bytes.extend(Length::Indefinite.to_bytes().as_ref());

            for ber in bers[0..i].iter() {
                bytes.extend(ber.as_ref() as &[u8]);
            }
            bytes.extend(eoc.as_ref() as &[u8]);

            let ber = unsafe { BerRef::from_bytes_starts_with_unchecked(bytes.as_ref()) };
            assert_eq!(bytes.as_ref() as &[u8], ber.as_ref() as &[u8]);
        }
    }

    #[test]
    fn try_from_deinite() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = ContentsRef::from_bytes(bytes);
            let ber = Ber::new(id, contents);
            let ber_ref = <&BerRef>::try_from(ber.as_ref() as &[u8]).unwrap();
            assert_eq!(ber_ref, ber.as_ref() as &BerRef);
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
            let mut bytes: Vec<u8> = Vec::from(id.as_ref() as &[u8]);

            bytes.extend(Length::Indefinite.to_bytes().as_ref());

            for ber in bers[0..i].iter() {
                bytes.extend(ber.as_ref() as &[u8]);
            }
            bytes.extend(eoc.as_ref() as &[u8]);

            let ber = <&BerRef>::try_from(bytes.as_ref() as &[u8]).unwrap();
            assert_eq!(bytes.as_ref() as &[u8], ber.as_ref() as &[u8]);
        }
    }
}
