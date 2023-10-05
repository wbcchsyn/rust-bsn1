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

use crate::{Buffer, Contents, ContentsRef, DerRef, Error, IdRef, Length};
use num::PrimInt;
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::ops::{Deref, DerefMut};

/// `Der` owns [`DerRef`] and represents ASN.1 DER.
///
/// The structure of `Der` is similar to that of `Vec<u8>`.
///
/// User can access the [`DerRef`] via the [`Deref`] and [`DerefMut`] implementation,
/// and to the inner slice via the [`DerRef`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    /// Parses `bytes` starting with DER octets and creates a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`try_from_bytes`].
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// [`try_from_bytes`]: Self::try_from_bytes
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let der_ref = <&DerRef>::try_from(bytes)?;
        Ok(der_ref.to_owned())
    }
}

impl Der {
    /// Creates a new instance from `id` and `contents`.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such identifiers.
    /// For example, 'Octet String' must be primitive in DER, but this function will construct a
    /// new instance even if `id` represents constructed 'Octet String.'
    ///
    /// # Panics
    ///
    /// Panics if the total length of the return value exceeds `isize::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ContentsRef, Der, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = ContentsRef::from_bytes(&[10, 20, 30]);
    ///
    /// let der = Der::new(id, contents);
    ///
    /// assert_eq!(id, der.id());
    /// assert_eq!(contents, der.contents());
    /// ```
    pub fn new(id: &IdRef, contents: &ContentsRef) -> Self {
        let len = Length::Definite(contents.len());
        let len = len.to_bytes();

        let total_len = id.len() + len.len() + contents.len();
        let mut buffer = Buffer::with_capacity(total_len);
        unsafe { buffer.set_len(total_len) };

        unsafe {
            let ptr = buffer.as_mut_ptr();
            ptr.copy_from_nonoverlapping(id.as_bytes().as_ptr(), id.len());

            let ptr = ptr.add(id.len());
            ptr.copy_from_nonoverlapping(len.as_ptr(), len.len());

            let ptr = ptr.add(len.len());
            ptr.copy_from_nonoverlapping(contents.as_bytes().as_ptr(), contents.len());
        }

        Self { buffer }
    }

    /// Creates a new instance from `id` and `contents` of `length` bytes.
    ///
    /// The `contents` of the return value is not initialized.
    /// Use [`mut_contents`] via [`DerefMut`] implementation to initialize them.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such identifiers.
    /// For example, 'Octet String' must be primitive in DER, but this function will construct a
    /// new instance even if `id` represents constructed 'Octet String.'
    ///
    /// # Panics
    ///
    /// Panics if the total bytes exceed `isize::MAX`.
    ///
    /// [`mut_contents`]: DerRef::mut_contents
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef, Length};
    ///
    /// let der = Der::with_id_length(IdRef::utf8_string(), 36);
    ///
    /// assert_eq!(der.id(), IdRef::utf8_string());
    /// assert_eq!(der.length(), Length::Definite(36));
    /// assert_eq!(der.contents().len(), 36);
    /// ```
    pub fn with_id_length(id: &IdRef, length: usize) -> Self {
        let length_ = Length::Definite(length).to_bytes();
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

    /// Parses `bytes` starting with DER octets and builds a new instance.
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
    /// [`TryFrom::try_from`]: #method.TryFrom
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Der;
    ///
    /// let bytes: &[u8] = &[0x02, 0x01, 0x0a];  // Represents '10' as Integer.
    /// let der0 = Der::try_from_bytes(bytes).unwrap();
    ///
    /// // Extra octets at the end does not affect the result.
    /// let bytes: &[u8] = &[0x02, 0x01, 0x0a, 0x01, 0x02];
    /// let der1 = Der::try_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(der0, der1);
    /// ```
    pub fn try_from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::try_from(bytes)
    }

    /// Builds a new instance holding `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'DER', use [`TryFrom`]
    /// implementation or [`try_from_bytes`] instead.
    ///
    /// [`TryFrom`]: #method.try_from-1
    /// [`try_from_bytes`]: #Self::try_from_bytes
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Der;
    ///
    /// let bytes: &[u8] = &[0x02, 0x01, 0x0a];  // Represents '10' as Integer.
    /// let der = unsafe { Der::from_bytes_unchecked(bytes) };
    /// assert_eq!(bytes, der.as_bytes());
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Creates a new instance from `id` and the iterator of `contents`.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function will construct a
    /// new instance even if `id` represents constructed 'Octet String.'
    ///
    /// # Panics
    ///
    /// Panics if the total length of the return value exceeds `isize::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ContentsRef, Der, IdRef};
    ///
    /// let id = IdRef::sequence();
    ///
    /// // Build instance using function 'from_id_iterator()'.
    /// let contents: &[Der] = &[Der::utf8_string("foo"), Der::integer(29_i32)];
    /// let der = Der::from_id_iterator(id, contents.iter());
    ///
    /// // Build instance using function 'new()'.
    /// let contents: Vec<u8> = contents.iter()
    ///                         .map(|i| Vec::from(i.as_bytes()))
    ///                         .flatten().collect();
    /// let contents = ContentsRef::from_bytes(&contents);
    /// let expected = Der::new(id, contents);
    ///
    /// // The result are same.
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
        let total_len = id.len() + length_bytes.len() + length;

        let mut buffer = Buffer::with_capacity(total_len);
        buffer.extend_from_slice(id.as_bytes());
        buffer.extend_from_slice(&length_bytes);
        contents.for_each(|c| buffer.extend_from_slice(c.as_ref()));

        Self { buffer }
    }

    /// Returns a new instance representing a boolean.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let val = true;
    /// let der = Der::boolean(val);
    ///
    /// assert_eq!(IdRef::boolean(), der.id());
    /// assert_eq!(val, der.contents().to_bool_der().unwrap());
    /// ```
    pub fn boolean(val: bool) -> Self {
        Self::new(IdRef::boolean(), &Contents::from_bool(val))
    }

    /// Returns a new instance representing integer.
    ///
    /// Type `T` should be a built-in primitive integer type (e.g., u8, u32, isize, i128, ...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let val = 39;
    /// let der = Der::integer(val);
    ///
    /// assert_eq!(IdRef::integer(), der.id());
    /// assert_eq!(val, der.contents().to_integer().unwrap());
    /// ```
    pub fn integer<T>(val: T) -> Self
    where
        T: PrimInt,
    {
        Self::new(IdRef::integer(), &Contents::from_integer(val))
    }

    /// Returns a new instance representing utf8_string.
    ///
    /// # Panics
    ///
    /// Panics if the total length of the return value exceeds `isize::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef};
    ///
    /// let val = "foo";
    /// let der = Der::utf8_string(val);
    ///
    /// assert_eq!(IdRef::utf8_string(), der.id());
    /// assert_eq!(val.as_bytes(), der.contents().as_bytes());
    /// ```
    pub fn utf8_string(val: &str) -> Self {
        Self::new(
            IdRef::utf8_string(),
            ContentsRef::from_bytes(val.as_bytes()),
        )
    }

    /// Returns a new instance representing octet_string.
    ///
    /// # Panics
    ///
    /// Panics if the total length of the return value exceeds `isize::MAX`.
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
    /// assert_eq!(val, der.contents().as_bytes());
    /// ```
    pub fn octet_string(val: &[u8]) -> Self {
        Self::new(IdRef::octet_string(), ContentsRef::from_bytes(val))
    }
}

impl AsRef<[u8]> for Der {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_bytes()
    }
}

impl Borrow<[u8]> for Der {
    fn borrow(&self) -> &[u8] {
        self.buffer.borrow()
    }
}

impl Borrow<DerRef> for Der {
    fn borrow(&self) -> &DerRef {
        self.deref()
    }
}

impl Deref for Der {
    type Target = DerRef;

    fn deref(&self) -> &Self::Target {
        unsafe { DerRef::from_bytes_unchecked(self.buffer.as_bytes()) }
    }
}

impl DerefMut for Der {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { DerRef::from_mut_bytes_unchecked(self.buffer.as_mut_bytes()) }
    }
}

impl PartialEq<DerRef> for Der {
    fn eq(&self, other: &DerRef) -> bool {
        self as &DerRef == other
    }
}

impl Der {
    /// Consumes `self`, returning `Vec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Der;
    ///
    /// let der = Der::octet_string(&[0, 1, 2, 3, 4]);
    /// let v = der.clone().into_vec();
    ///
    /// assert_eq!(der.as_bytes(), &v);
    /// ```
    pub fn into_vec(self) -> Vec<u8> {
        self.buffer.into_vec()
    }

    /// Forces to set the length of the `contents` to `new_length`.
    ///
    /// If `new_length` is less than the length of current `contents`, this method truncates the
    /// contents; otherwise, the `contents` is enlarged. The bytes of the extended
    /// contents are not initialized. Use [`mut_contents`] via [`DerefMut`] implementation
    /// to initialize them.
    ///
    /// # Warnings
    ///
    /// `new_length` implies the length of `contents`.
    /// The total length will be greater than `new_length`.
    ///
    /// # Panics
    ///
    /// Panics if the total length exceed `isize::MAX`.
    ///
    /// [`mut_contents`]: DerRef::mut_contents
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, Length};
    ///
    /// let mut der = Der::octet_string(&[]);
    ///
    /// assert_eq!(der.length(), Length::Definite(0));
    /// assert_eq!(der.contents().as_bytes(), &[]);
    ///
    /// let new_contents: &[u8] = &[1, 2, 3, 4];
    /// der.set_length(new_contents.len());
    /// der.mut_contents().as_mut_bytes().copy_from_slice(new_contents);
    ///
    /// assert_eq!(der.length(), Length::Definite(new_contents.len()));
    /// assert_eq!(der.contents().as_bytes(), new_contents);
    /// ```
    pub fn set_length(&mut self, new_length: usize) {
        let old_length = self.contents().len();
        if old_length == new_length {
            return;
        }

        let contents_offset = (new_length as isize) - (old_length as isize);

        let old_length_ = Length::Definite(old_length).to_bytes();
        let new_length_ = Length::Definite(new_length).to_bytes();
        let length_offset = (new_length_.len() as isize) - (old_length_.len() as isize);

        // Reserve the capacity if necessary
        if 0 < contents_offset {
            let total_offset = length_offset + contents_offset;
            self.buffer.reserve(total_offset as usize);
        }

        unsafe {
            // Copy the contents if necessary.
            if length_offset != 0 {
                let src = self.mut_contents().as_mut_bytes().as_mut_ptr();
                let dst = src.offset(length_offset);
                let count = new_length.min(old_length);
                dst.copy_from(src, count);
            }

            // Copy the length
            let src = new_length_.as_ptr();
            let dst = self.buffer.as_mut_ptr().add(self.id().len());
            dst.copy_from_nonoverlapping(src, new_length_.len());

            // Update the buffer length
            let total_len = (self.buffer.len() as isize) + length_offset + contents_offset;
            self.buffer.set_len(total_len as usize);
        }
    }
}

pub fn disassemble_der(der: Der) -> Buffer {
    der.buffer
}

/// Builds a `Der` instance representing 'Constructed DER' effectively.
///
/// # Formula
///
/// `constructed_der!(id: &IdRef [, (id_1, contents_1) [, (id_2, contents_2) [...]]]) => Der`
///
/// `id_n` and `contents_n` must be bounded on `AsRef<[u8]>`.
///
/// # Warnings
///
/// ASN.1 does not allow some universal identifiers for DER, however, this macro accepts
/// such an identifier.
/// For example, 'Octet String' must be primitive in DER, but this function will construct a
/// new instance even if `id` represents constructed 'Octet String.'
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
/// let der = constructed_der!(id);
///
/// assert_eq!(der.id(), id);
/// assert!(der.contents().is_empty());
/// ```
///
/// Sequence of 2 DERs.
///
/// ```
/// # #[macro_use] extern crate bsn1;
/// use bsn1::{Contents, ContentsRef, DerRef, IdRef};
///
/// let id = IdRef::sequence();
/// let id1 = IdRef::octet_string();
/// let contents1 = &[1, 2, 3];
/// let id2 = IdRef::integer();
/// let contents2 = Contents::from_integer(10);
///
/// let der = constructed_der!(id, (id1.to_owned(), contents1), (id2, &contents2));
///
/// assert_eq!(id, der.id());
///
/// let bytes = der.contents().as_bytes();
/// let der1 = DerRef::try_from_bytes(bytes).unwrap();
/// assert_eq!(id1, der1.id());
/// assert_eq!(contents1, der1.contents().as_bytes());
///
/// let bytes = &bytes[der1.as_bytes().len()..];
/// let der2 = DerRef::try_from_bytes(bytes).unwrap();
/// assert_eq!(id2, der2.id());
/// assert_eq!(&contents2 as &ContentsRef, der2.contents());
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
            let contents = ContentsRef::from_bytes(bytes);
            let der = Der::new(id, contents);
            assert_eq!(id, der.id());
            assert_eq!(Length::Definite(bytes.len()), der.length());
            assert_eq!(contents, der.contents());
        }
    }

    #[test]
    fn from_id_iterator() {
        let id = IdRef::octet_string();

        // Empty contents
        {
            let contents: &[&[u8]] = &[];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, ContentsRef::from_bytes(&[]));
            assert_eq!(expected, der);
        }

        // Single slice of empty bytes.
        {
            let contents: &[&[u8]] = &[&[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, ContentsRef::from_bytes(&[]));
            assert_eq!(expected, der);
        }

        // Single slice of not empty bytes.
        {
            let contents: &[&[u8]] = &[&[1, 2, 3]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, ContentsRef::from_bytes(&[1, 2, 3]));
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // Both elements are empty.
        {
            let contents: &[&[u8]] = &[&[], &[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, ContentsRef::from_bytes(&[]));
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // One of the elements is empty
        {
            let contents: &[&[u8]] = &[&[], &[1, 2]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, ContentsRef::from_bytes(&[1, 2]));
            assert_eq!(expected, der);

            let contents: &[&[u8]] = &[&[3], &[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, ContentsRef::from_bytes(&[3]));
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // Neither element is empty
        {
            let contents: &[&[u8]] = &[&[1, 2], &[3]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, ContentsRef::from_bytes(&[1, 2, 3]));
            assert_eq!(expected, der);
        }
    }

    #[test]
    fn try_from() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = ContentsRef::from_bytes(bytes);
            let der = Der::new(id, contents);
            let der_ref = <&DerRef>::try_from(der.as_bytes()).unwrap();
            assert_eq!(der_ref, &der as &DerRef);
        }
    }

    #[test]
    fn extend_der() {
        let mut der = Der::octet_string(&[]);

        for i in 0..=256 {
            der.set_length(i + 1);
            der.mut_contents()[i] = i as u8;

            assert_eq!(der.length(), Length::Definite(i + 1));

            let contents = der.contents();
            for j in 0..=i {
                assert_eq!(contents[j], j as u8);
            }
        }

        {
            der.set_length(65535);
            assert_eq!(der.length(), Length::Definite(65535));

            let contents = der.contents();
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            der.set_length(65536);
            assert_eq!(der.length(), Length::Definite(65536));

            let contents = der.contents();
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            der.set_length(256.pow(3) - 1);
            assert_eq!(der.length(), Length::Definite(256.pow(3) - 1));

            let contents = der.contents();
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            der.set_length(256.pow(3));
            assert_eq!(der.length(), Length::Definite(256.pow(3)));

            let contents = der.contents();
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }
    }

    #[test]
    fn shrinik_der() {
        let contents: Vec<u8> = (0..=std::u8::MAX).cycle().take(256.pow(3) + 1).collect();
        let mut der = Der::octet_string(&contents);

        {
            let len = 256.pow(3);
            der.set_length(len);
            assert_eq!(der.length(), Length::Definite(len));

            let contents = der.contents();
            for i in 0..len {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            let len = 256.pow(3) - 1;
            der.set_length(len);
            assert_eq!(der.length(), Length::Definite(len));

            let contents = der.contents();
            for i in 0..len {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            let len = 65536;
            der.set_length(len);
            assert_eq!(der.length(), Length::Definite(len));

            let contents = der.contents();
            for i in 0..len {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            let len = 65535;
            der.set_length(len);
            assert_eq!(der.length(), Length::Definite(len));

            let contents = der.contents();
            for i in 0..len {
                assert_eq!(contents[i], i as u8);
            }
        }

        for len in (0..=256).rev() {
            der.set_length(len);
            assert_eq!(der.length(), Length::Definite(len));

            let contents = der.contents();
            for i in 0..len {
                assert_eq!(contents[i], i as u8);
            }
        }
    }
}
