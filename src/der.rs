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

use crate::{contents, identifier, length, Buffer, Error, IdRef, Length};
use core::convert::TryFrom;
use core::ops::Deref;
use num::PrimInt;
use std::borrow::Borrow;

/// `DerRef` is a wrapper of `[u8]` and represents DER.
///
/// This struct is 'Unsized', and user usually uses a reference to the instance.
#[derive(Debug, PartialEq, Eq)]
pub struct DerRef {
    bytes: [u8],
}

impl<'a> TryFrom<&'a [u8]> for &'a DerRef {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a reference to `DerRef` .
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function will accept
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        let id = <&IdRef>::try_from(bytes)?;
        let parsing = &bytes[id.as_ref().len()..];

        let (len, parsing) = match length::try_from(parsing) {
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

impl DerRef {
    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a reference to `DerRef` .
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`<&DerRef>::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function will accept
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`<&DerRef>::try_from`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<&Self, Error> {
        <&Self>::try_from(bytes)
    }

    /// Provides a reference from `bytes` without any sanitization.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'DER' or not, use [`TryFrom`]
    /// implementation or [`from_bytes`].
    ///
    /// The difference from [`from_bytes_starts_with_unchecked`] is that
    /// [`from_bytes_starts_with_unchecked`] checks the 'LENGTH' octets and excludes extra
    /// octet(s) at the end if any while this method does not check at all (i.e.
    /// [`from_bytes_starts_with_unchecked`] allows extra octets at the end.)
    ///
    /// [`from_bytes_starts_with_unchecked`]: #method.from_bytes_starts_with_unchecked
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    /// [`from_bytes`]: #method.from_bytes
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, IdRef};
    ///
    /// let der = Der::new(IdRef::octet_string(), &[]);
    /// let der_ref = unsafe { DerRef::from_bytes_unchecked(der.as_ref()) };
    /// assert_eq!(der.as_ref() as &DerRef, der_ref);
    /// ```
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        let ptr = bytes as *const [u8];
        let ptr = ptr as *const Self;
        &*ptr
    }

    /// Provides a reference from `bytes` that starts with a DER.
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
    /// The behavior is undefined if `bytes` does not start with 'ASN.1 DER' octets.
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    /// [`from_bytes_unchecked`]: #method.from_bytes_unchecked
    /// [`from_bytes`]: #method.from_bytes
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, IdRef};
    ///
    /// let der = Der::new(IdRef::octet_string(), &[]);
    /// let mut bytes = Vec::from(der.as_ref() as &[u8]);
    /// bytes.extend(&[1, 2, 3]);
    ///
    /// let der_ref = unsafe { DerRef::from_bytes_starts_with_unchecked(bytes.as_ref()) };
    /// assert_eq!(der.as_ref() as &DerRef, der_ref);
    /// ```
    #[inline]
    pub unsafe fn from_bytes_starts_with_unchecked(bytes: &[u8]) -> &Self {
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
}

impl AsRef<[u8]> for DerRef {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl Borrow<[u8]> for DerRef {
    #[inline]
    fn borrow(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for DerRef {
    type Owned = Der;

    fn to_owned(&self) -> Self::Owned {
        let buffer = Buffer::from(&self.bytes);
        Der { buffer }
    }
}

impl PartialEq<Der> for DerRef {
    #[inline]
    fn eq(&self, other: &Der) -> bool {
        self == other.as_ref() as &DerRef
    }
}

impl DerRef {
    /// Returns a reference to `IdRef` of `self` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = &[1, 2, 3];
    ///
    /// // 'DER' implements 'Deref<Target=DerRef>'
    /// let der = Der::new(id, contents);
    /// assert_eq!(id, der.id());
    /// ```
    #[inline]
    pub fn id(&self) -> &IdRef {
        unsafe {
            let bytes = identifier::shrink_to_fit_unchecked(&self.bytes);
            IdRef::from_bytes_unchecked(bytes)
        }
    }

    /// Returns `Length` to represent the length of contents.
    ///
    /// Note that DER does not allow indefinite Length.
    /// The return value must be `Length::Definite` .
    ///
    /// # Warnings
    ///
    /// `Length` stands for the length octets in DER.
    /// The total bytes is greater than the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef, Length};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = &[1, 2, 3];
    ///
    /// // 'DER' implements 'Deref<Target=DerRef>'
    /// let der = Der::new(id, contents);
    /// assert_eq!(Length::Definite(contents.len()), der.length());
    /// ```
    #[inline]
    pub fn length(&self) -> Length {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        unsafe { length::from_bytes_starts_with_unchecked(bytes).0 }
    }

    /// Returns a reference to the contents octets of `self` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = &[1, 2, 3];
    ///
    /// // 'DER' implements 'Deref<Target=DerRef>'
    /// let der = Der::new(id, contents);
    /// assert_eq!(contents, der.contents());
    /// ```
    #[inline]
    pub fn contents(&self) -> &[u8] {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        unsafe { length::from_bytes_starts_with_unchecked(bytes).1 }
    }
}

/// `Der` owns [`DerRef`] and represents DER.
///
/// [`DerRef`]: struct.DerRef.html
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Der {
    buffer: Buffer,
}

impl From<&DerRef> for Der {
    fn from(der_ref: &DerRef) -> Self {
        der_ref.to_owned()
    }
}

impl TryFrom<&[u8]> for Der {
    type Error = Error;

    /// Parses `bytes` starting with DER octets and builds a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`from_bytes`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`from_bytes`]: #method.from_bytes
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let der_ref = <&DerRef>::try_from(bytes)?;
        Ok(der_ref.to_owned())
    }
}

impl Der {
    /// Creates a new instance from `id` and `contents` .
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function will construct a
    /// new instance even if `id` represenets constructed 'Octet String.'
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents: &[u8] = &[10, 20, 30];
    ///
    /// let der = Der::new(id, contents);
    ///
    /// assert_eq!(id, der.id());
    /// assert_eq!(contents, der.contents());
    /// ```
    pub fn new(id: &IdRef, contents: &[u8]) -> Self {
        let len = Length::Definite(contents.len());
        let len = len.to_bytes();

        let total_len = id.as_ref().len() + len.as_ref().len() + contents.len();
        let mut buffer = Buffer::with_capacity(total_len);
        unsafe { buffer.set_len(total_len) };

        unsafe {
            let ptr = buffer.as_mut_ptr();
            let id = id.as_ref();
            ptr.copy_from_nonoverlapping(id.as_ptr(), id.len());

            let ptr = ptr.add(id.len());
            ptr.copy_from_nonoverlapping(len.as_ref().as_ptr(), len.as_ref().len());

            let ptr = ptr.add(len.as_ref().len());
            ptr.copy_from_nonoverlapping(contents.as_ptr(), contents.len());
        }

        Self { buffer }
    }

    /// Parses `bytes` starting with DER octets and builds a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is same to [`TryFrom::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`TryFrom::try_from`]: #impl-TryFrom%3C%26%27_%20%5Bu8%5D%3E
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::try_from(bytes)
    }

    /// Creates a new instance from `id` and `contents` .
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifier for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function will construct a
    /// new instance even if `id` represenets constructed 'Octet String.'
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let id = IdRef::sequence();
    ///
    /// // Build instance using function 'from_id_iterator()'.
    /// let contents: &[Der] = &[Der::utf8_string("foo"), Der::integer(29)];
    /// let der = Der::from_id_iterator(id, contents.iter());
    ///
    /// // Build instance using function 'new()'.
    /// let contents: Vec<u8> = contents.iter()
    ///                         .map(|i| Vec::from(i.as_ref() as &[u8]))
    ///                         .flatten().collect();
    /// let expected = Der::new(id, &contents);
    ///
    /// assert_eq!(expected, der);
    /// ```
    pub fn from_id_iterator<I>(id: &IdRef, contents: I) -> Self
    where
        I: Iterator + Clone,
        I::Item: AsRef<[u8]>,
    {
        let length = contents
            .clone()
            .fold(0, |acc, item| acc + item.as_ref().len());
        let length_bytes = Length::Definite(length).to_bytes();
        let total_len = id.as_ref().len() + length_bytes.as_ref().len() + length;

        let mut buffer = Buffer::with_capacity(total_len);
        buffer.extend_from_slice(id.as_ref());
        buffer.extend_from_slice(length_bytes.as_ref());
        for c in contents {
            buffer.extend_from_slice(c.as_ref());
        }

        Self { buffer }
    }

    /// Returns a new instance representing boolean.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{contents, Der, IdRef};
    ///
    /// let val = true;
    /// let der = Der::boolean(val);
    ///
    /// assert_eq!(IdRef::boolean(), der.id());
    /// assert_eq!(val, contents::to_bool_der(der.contents()).unwrap());
    /// ```
    pub fn boolean(val: bool) -> Self {
        Self::new(IdRef::boolean(), contents::from_bool(val).as_ref())
    }

    /// Returns a new instance representing integer.
    ///
    /// Type `T` should be the builtin primitive integer types (e.g., u8, u32, isize, i128, ...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{contents, Der, IdRef};
    ///
    /// let val = 39;
    /// let der = Der::integer(val);
    ///
    /// assert_eq!(IdRef::integer(), der.id());
    /// assert_eq!(val, contents::to_integer(der.contents()).unwrap());
    /// ```
    pub fn integer<T>(val: T) -> Self
    where
        T: PrimInt,
    {
        Self::new(IdRef::integer(), contents::from_integer(val).as_ref())
    }

    /// Returns a new instance representing utf8_string.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let val = &"foo";
    /// let der = Der::utf8_string(val);
    ///
    /// assert_eq!(IdRef::utf8_string(), der.id());
    /// assert_eq!(val.as_bytes(), der.contents());
    /// ```
    pub fn utf8_string(val: &str) -> Self {
        Self::new(IdRef::utf8_string(), val.as_bytes())
    }

    /// Returns a new instance representing octet_string.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let val = &[1, 2, 3];
    /// let der = Der::octet_string(val);
    ///
    /// assert_eq!(IdRef::octet_string(), der.id());
    /// assert_eq!(val, der.contents());
    /// ```
    pub fn octet_string(val: &[u8]) -> Self {
        Self::new(IdRef::octet_string(), val)
    }
}

impl AsRef<[u8]> for Der {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

impl AsRef<DerRef> for Der {
    #[inline]
    fn as_ref(&self) -> &DerRef {
        self.deref()
    }
}

impl Borrow<[u8]> for Der {
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.buffer.borrow()
    }
}

impl Borrow<DerRef> for Der {
    #[inline]
    fn borrow(&self) -> &DerRef {
        self.deref()
    }
}

impl Deref for Der {
    type Target = DerRef;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { DerRef::from_bytes_unchecked(self.buffer.as_ref()) }
    }
}

impl PartialEq<DerRef> for Der {
    #[inline]
    fn eq(&self, other: &DerRef) -> bool {
        self.as_ref() as &DerRef == other
    }
}

impl Der {
    /// Consumes `self` , returning `Vec` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents: &[u8] = &[0, 1, 2, 3, 4];
    ///
    /// let der = Der::new(id, contents);
    /// let v = der.clone().into_vec();
    ///
    /// assert_eq!(der.as_ref() as &[u8], v.as_ref() as &[u8]);
    /// ```
    pub fn into_vec(self) -> Vec<u8> {
        self.buffer.into_vec()
    }
}

#[inline]
pub fn disassemble_der(der: Der) -> Buffer {
    der.buffer
}

/// Builds a `Der` instance representing 'Constructed DER' effectively.
///
/// # Formula
///
/// `constructed_der!(id: &IdRef [, (id_1, contents_1) [, (id_2, contents_2) [...]]]) => Der`
///
/// `id_n` and `contents_n` must be bounded on `AsRef<[u8]>` .
///
/// # Warnings
///
/// ASN.1 does not allow some universal identifier for DER, however, this macro accepts
/// such an identifier.
/// For example, 'Octet String' must be primitive in DER, but this function will construct a
/// new instance even if `id` represenets constructed 'Octet String.'
///
/// # Examples
///
/// Empty contents.
///
/// ```
/// # #[macro_use] extern crate bsn1;
/// use bsn1::{Der, IdRef};
///
/// let id = IdRef::sequence();
/// let expected = Der::new(id, &[]);
/// let der = constructed_der!(id);
///
/// assert_eq!(expected, der);
/// ```
///
/// Sequence of 2 DERs.
///
/// ```
/// # #[macro_use] extern crate bsn1;
/// use bsn1::{contents, DerRef, IdRef};
/// use std::convert::TryFrom;
///
/// let id = IdRef::sequence();
/// let id1 = IdRef::octet_string();
/// let contents1: [u8; 3] = [1, 2, 3];
/// let id2 = IdRef::integer();
/// let contents2 = contents::from_integer(10);
///
/// let der = constructed_der!(id, (id1.to_owned(), contents1), (id2, &contents2));
///
/// assert_eq!(id, der.id());
///
/// let bytes = der.contents();
/// let der1 = <&DerRef>::try_from(bytes).unwrap();
/// assert_eq!(id1, der1.id());
/// assert_eq!(contents1, der1.contents());
///
/// let bytes = &bytes[der1.as_ref().len()..];
/// let der2 = <&DerRef>::try_from(bytes).unwrap();
/// assert_eq!(id2, der2.id());
/// assert_eq!(contents2.as_ref(), der2.contents());
/// ```
#[macro_export]
macro_rules! constructed_der {
    ($id:expr $(, ($id_n:expr, $contents_n:expr))*) => {{
        let id = $id;
        __bsn1__expand_constructed_der!($(($id_n, $contents_n)),* ; id)
    }};
    ($id:expr $(, ($id_n:expr, $contents_n:expr))*,) => {
        constructed_der!($id, $(($id_n, $contents_n)),*)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __bsn1__expand_constructed_der {
    (; $id:tt $($contents:tt)*) => {{
        let contents: &[&[u8]] = &[$($contents),*];
        bsn1::Der::from_id_iterator($id, contents.iter())
    }};

    (($id_1:expr, $contents_1:expr) $(, ($id_n:expr, $contents_n:expr))* ; $id:tt $($acc:tt)*) => {{
        use bsn1::Length;

        let id_1 = $id_1;
        let id_1: &[u8] = id_1.as_ref();

        let contents_1 = $contents_1;
        let contents_1: &[u8] = contents_1.as_ref();

        let length_1 = Length::Definite(contents_1.len());
        let length_1 = length_1.to_bytes();
        let length_1: &[u8] = length_1.as_ref();

        __bsn1__expand_constructed_der!(
            $(($id_n, $contents_n)),*
            ;
            $id
            $($acc)*
            id_1
            length_1
            contents_1
        )
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let der = Der::new(id, bytes);
            assert_eq!(id, der.id());
            assert_eq!(Length::Definite(bytes.len()), der.length());
            assert_eq!(bytes, der.contents());
        }
    }

    #[test]
    fn from_id_iterator() {
        let id = IdRef::octet_string();

        // Empty contents
        {
            let contents: &[&[u8]] = &[];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, &[]);
            assert_eq!(expected, der);
        }

        // Single slice of empty bytes.
        {
            let contents: &[&[u8]] = &[&[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, &[]);
            assert_eq!(expected, der);
        }

        // Single slice of not empty bytes.
        {
            let contents: &[&[u8]] = &[&[1, 2, 3]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, &[1, 2, 3]);
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // Both elements are empty.
        {
            let contents: &[&[u8]] = &[&[], &[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, &[]);
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // One of the elements is empty
        {
            let contents: &[&[u8]] = &[&[], &[1, 2]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, &[1, 2]);
            assert_eq!(expected, der);

            let contents: &[&[u8]] = &[&[3], &[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, &[3]);
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // Neither element is empty
        {
            let contents: &[&[u8]] = &[&[1, 2], &[3]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, &[1, 2, 3]);
            assert_eq!(expected, der);
        }
    }

    #[test]
    fn try_from() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let der = Der::new(id, bytes);
            let der_ref = <&DerRef>::try_from(der.as_ref() as &[u8]).unwrap();
            assert_eq!(der_ref, der.as_ref() as &DerRef);
        }
    }

    #[test]
    fn from_bytes_starts_with_unchecked() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        let extras: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let der = Der::new(id, bytes);

            for &extra in extras {
                let mut bytes = Vec::from(der.as_ref() as &[u8]);
                bytes.extend(extra);

                let der_ref = unsafe { DerRef::from_bytes_starts_with_unchecked(bytes.as_ref()) };
                assert_eq!(der_ref, &der);
            }
        }
    }
}
