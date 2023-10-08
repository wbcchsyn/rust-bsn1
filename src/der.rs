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
use std::borrow::Borrow;
use std::io::Read;
use std::ops::{Deref, DerefMut};

/// `Der` owns [`DerRef`] and represents ASN.1 DER.
///
/// The structure of `Der` is similar to that of `Vec<u8>`.
///
/// User can access the inner [`DerRef`] via the `Deref` and `DerefMut` implementation.
#[derive(Debug, Clone, Eq, Hash)]
pub struct Der {
    buffer: Buffer,
}

impl From<&DerRef> for Der {
    fn from(der_ref: &DerRef) -> Self {
        der_ref.to_owned()
    }
}

impl From<bool> for Der {
    /// Creates a new instance representing boolean containing `contents`.
    fn from(contents: bool) -> Self {
        Self::new(IdRef::boolean(), <&ContentsRef>::from(contents))
    }
}

impl From<i8> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: i8) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<u8> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: u8) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<i16> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: i16) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<u16> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: u16) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<i32> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: i32) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<u32> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: u32) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<i64> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: i64) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<u64> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: u64) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<i128> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: i128) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<u128> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: u128) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<isize> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: isize) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<usize> for Der {
    /// Creates a new instance representing integer containing `contents`.
    fn from(contents: usize) -> Self {
        Self::new(IdRef::integer(), &Contents::from(contents))
    }
}

impl From<&str> for Der {
    /// Creates a new instance representing utf8-string containing `contents`.
    fn from(contents: &str) -> Self {
        Self::new(
            IdRef::utf8_string(),
            <&ContentsRef>::from(contents.as_bytes()),
        )
    }
}

impl From<&[u8]> for Der {
    fn from(contents: &[u8]) -> Self {
        Self::new(IdRef::octet_string(), <&ContentsRef>::from(contents))
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
    /// let contents = <&ContentsRef>::from(&[10, 20, 30]);
    ///
    /// let der = Der::new(id, contents);
    ///
    /// assert_eq!(id, der.id());
    /// assert_eq!(contents, der.contents());
    /// ```
    pub fn new(id: &IdRef, contents: &ContentsRef) -> Self {
        let mut ret = Self::with_id_length(id, contents.len());

        ret.mut_contents()
            .as_mut()
            .copy_from_slice(contents.as_ref());

        ret
    }

    /// Creates a new instance from `id` and `contents` of `length` bytes.
    ///
    /// The `contents` of the return value is not initialized.
    /// Use [`mut_contents`] via `DerefMut` implementation to initialize them.
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
    /// let mut der = Der::with_id_length(IdRef::octet_string(), 5);
    ///
    /// assert_eq!(der.id(), IdRef::octet_string());
    /// assert_eq!(der.length(), Length::Definite(5));
    /// assert_eq!(der.contents().len(), 5);
    ///
    /// der.mut_contents().as_mut().copy_from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(der.contents().as_ref(), &[1, 2, 3, 4, 5]);
    /// ```
    pub fn with_id_length(id: &IdRef, length: usize) -> Self {
        let length_ = Length::Definite(length).to_bytes();
        let total_len = id.len() + length_.len() + length;

        let mut buffer = Buffer::with_capacity(total_len);

        unsafe {
            let dst = buffer.as_mut_ptr();
            dst.copy_from_nonoverlapping(id.as_ref().as_ptr(), id.len());

            let dst = dst.add(id.len());
            dst.copy_from_nonoverlapping(length_.as_ptr(), length_.len());

            buffer.set_len(total_len);
        }

        Self { buffer }
    }

    /// Parses `readable` starting with DER octets and builds a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Performance
    ///
    /// This function is not so efficient compared with [`DerRef::parse`].
    /// If you have a slice of serialized DER, use [`DerRef::parse`]
    /// and then call [`ToOwned::to_owned`] instead.
    ///
    /// [`DerRef::parse`]: DerRef::parse
    /// [`ToOwned::to_owned`]: std::borrow::ToOwned::to_owned
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
    /// // Serialize DER of '10' as Integer.
    /// let der = Der::from(10_i32);
    /// let mut serialized = Vec::from(der.as_ref() as &[u8]);
    ///
    /// // Deserialize.
    /// let deserialized = Der::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(der, deserialized);
    ///
    /// // Extra octets at the end does not affect the result.
    /// serialized.push(0x00);
    /// serialized.push(0x01);
    /// let deserialized = Der::parse(&mut &serialized[..]).unwrap();
    ///
    /// assert_eq!(der, deserialized);
    ///
    /// // We can access to the inner slice of `serialized`.
    /// // We can use `DerRef::parse` instead of this function.
    /// // (`DerRef::parse` is more efficient than this function.)
    /// let deserialized = DerRef::parse(&serialized[..]).map(ToOwned::to_owned).unwrap();
    /// assert_eq!(der, deserialized);
    /// ```
    pub fn parse<R: Read>(readable: &mut R) -> Result<Self, Error> {
        let mut writeable = Buffer::new();

        let contents_length =
            match unsafe { crate::misc::parse_id_length(readable, &mut writeable)? } {
                Length::Indefinite => return Err(Error::IndefiniteLength),
                Length::Definite(length) => length,
            };

        let id_length_len = writeable.len();
        let total_length = id_length_len + contents_length;

        writeable.reserve(contents_length);
        unsafe { writeable.set_len(total_length) };

        let buffer = &mut writeable.as_mut_bytes()[id_length_len..];
        match readable.read(buffer) {
            Err(e) => Err(e.into()),
            Ok(read) => {
                if read < contents_length {
                    Err(Error::UnTerminatedBytes)
                } else {
                    Ok(Self { buffer: writeable })
                }
            }
        }
    }

    /// Builds a new instance holding `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'DER', use [`parse`] instead.
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
    /// use bsn1::Der;
    ///
    /// let der = Der::from(10_i32);
    /// let serialized: &[u8]  = der.as_ref();
    /// let deserialized = unsafe { Der::from_bytes_unchecked(&serialized) };
    /// assert_eq!(der, deserialized);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Builds a new instance holding `bytes` without any check.
    ///
    /// `bytes` must not includ any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'DER', use [`parse`] instead.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Der;
    ///
    /// let der = Der::from(5_i32);
    /// let serialized = der.clone().into_vec();
    /// let deserialized = unsafe { Der::from_vec_unchecked(serialized) };
    ///
    /// assert_eq!(der, deserialized);
    /// ```
    pub unsafe fn from_vec_unchecked(bytes: Vec<u8>) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Creates a new instance containing concatenated `contents`.
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
    /// // Build an sequence DER containing 2 other DERs.
    /// let contents0 = vec![Der::from("foo"), Der::from(29_i32)];
    /// let der0 = Der::from_id_iterator(IdRef::sequence(), contents0.iter());
    ///
    /// let mut contents1: Vec<u8> = Der::from("foo").into_vec();
    /// contents1.extend_from_slice(&Der::from(29_i32).into_vec());
    /// let der1 = Der::new(IdRef::sequence(), <&ContentsRef>::from(&contents1[..]));
    ///
    /// assert_eq!(der0, der1);
    ///
    /// // Build an utf8-string DER using function `from_id_iterator()`.
    /// let contents = vec!["Foo", "Bar"];
    /// let der = Der::from_id_iterator(
    ///             IdRef::utf8_string(), contents.iter().map(|s| s.as_bytes()));
    /// assert_eq!(der, Der::from("FooBar"));
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
        buffer.extend_from_slice(id.as_ref());
        buffer.extend_from_slice(&length_bytes);
        contents.for_each(|c| buffer.extend_from_slice(c.as_ref()));

        Self { buffer }
    }
}

impl AsRef<[u8]> for Der {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_bytes()
    }
}

impl AsRef<DerRef> for Der {
    fn as_ref(&self) -> &DerRef {
        self.deref()
    }
}

impl AsMut<DerRef> for Der {
    fn as_mut(&mut self) -> &mut DerRef {
        self.deref_mut()
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

impl<T> PartialEq<T> for Der
where
    T: Borrow<DerRef>,
{
    fn eq(&self, other: &T) -> bool {
        self.deref() == other.borrow()
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
    /// let der = Der::from("foo");
    /// let v = der.clone().into_vec();
    ///
    /// assert_eq!(der.as_ref() as &[u8], &v);
    /// ```
    pub fn into_vec(self) -> Vec<u8> {
        self.buffer.into_vec()
    }

    /// Appends `byte` to the end of the 'contents octets'.
    ///
    /// Note that this method may shift the 'contents octets',
    /// and the performance is `O(n)` where `n` is the byte count of 'contents octets'
    /// in the worst-case,
    /// because the byte count of 'length octets' may change.
    /// (DER is composed of 'identifier octets', 'length octets' and 'contents octets'
    /// in this order.)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef, Length};
    ///
    /// let bytes: Vec<u8> = (0..10).collect();
    /// let mut der = Der::from(&bytes[..]);
    /// der.push(0xff);
    ///
    /// assert_eq!(der.id(), IdRef::octet_string());
    /// assert_eq!(der.length(), Length::Definite(bytes.len() + 1));
    ///
    /// assert_eq!(&der.contents().as_ref()[..bytes.len()], &bytes[..]);
    /// assert_eq!(der.contents().as_ref().last().unwrap(), &0xff);
    /// ```
    pub fn push(&mut self, byte: u8) {
        self.extend_from_slice(&[byte]);
    }

    /// Appends `bytes` to the end of the 'contents octets'.
    ///
    /// Note that this method may shift the 'contents octets',
    /// and the performance is `O(n)` where `n` is the byte count of 'contents octets'
    /// in the worst-case,
    /// because the byte count of 'length octets' may change.
    /// (DER is composed of 'identifier octets', 'length octets' and 'contents octets'
    /// in this order.)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef, Length};
    ///
    /// let bytes: Vec<u8> = (0..10).collect();
    /// let mut der = Der::from(&bytes[..5]);
    /// der.extend_from_slice(&bytes[5..]);
    ///
    /// assert_eq!(der.id(), IdRef::octet_string());
    /// assert_eq!(der.length(), Length::Definite(bytes.len()));
    /// assert_eq!(der.contents().as_ref(), &bytes[..]);
    /// ```
    pub fn extend_from_slice(&mut self, bytes: &[u8]) {
        let id_len = self.id().len();
        let old_length = self.length();
        let new_length = Length::Definite(old_length.definite().unwrap() + bytes.len());

        // Update the length of `buffer`
        {
            let offset = bytes.len() + new_length.len() - old_length.len();
            self.buffer.reserve(offset);
            unsafe { self.buffer.set_len(self.buffer.len() + offset) };
        }

        unsafe {
            // Copy the contents
            {
                let mut dest = self.buffer.as_mut_ptr().add(id_len).add(new_length.len());

                // Copy the old  contents octets if necessary.
                {
                    let src = self.buffer.as_ptr().add(id_len + old_length.len());
                    let count = old_length.definite().unwrap();
                    if src != dest {
                        src.copy_to(dest, count);
                    }
                    dest = dest.add(count);
                }

                // Copy `bytes`
                {
                    let src = bytes.as_ptr();
                    let count = bytes.len();
                    src.copy_to_nonoverlapping(dest, count);
                    dest = dest.add(count);
                }

                debug_assert_eq!(
                    dest.offset_from(self.buffer.as_ptr()),
                    self.buffer.len() as isize
                );
            }

            // Copy the length octets
            {
                let new_length_bytes = new_length.to_bytes();
                let src = new_length_bytes.as_ptr();
                let dest = self.buffer.as_mut_ptr().add(id_len);
                src.copy_to(dest, new_length_bytes.len());
            }
        }
    }

    /// Enshorten the `contents`, keeping the first `new_length` and discarding the rest
    /// if `new_length` is less than the length of the current 'contents octets';
    /// otherwise, does nothing.
    ///
    /// Note that this method may shift the 'contents octets',
    /// and the performance is `O(n)` where `n` is the byte count of 'contents octets'
    /// in the worst-case,
    /// because the byte count of 'length octets' may change.
    /// (DER is composed of 'identifier octets', 'length octets' and 'contents octets'
    /// in this order.)
    ///
    /// # Warnings
    ///
    /// `new_length` specifies the length of the 'contents octets' after this method returns.
    /// The total length of `self` will be greater than `new_length`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, IdRef, Length};
    ///
    /// // Create a DER of '0..=255' as Octet String.
    /// let bytes: Vec<u8> = (0..=255).collect();
    /// let mut der = Der::from(&bytes[..]);
    ///
    /// // Truncate the length
    /// der.truncate(100);
    ///
    /// assert_eq!(der.id(), IdRef::octet_string());        // The identifier is not changed.
    /// assert_eq!(der.length(), Length::Definite(100));    // The length is changed.
    /// assert_eq!(der.contents().as_ref(), &bytes[..100]); // The contents is changed.
    /// ```
    pub fn truncate(&mut self, new_length: usize) {
        let id_len = self.id().len();
        let old_length = self.length().definite().unwrap();

        if old_length <= new_length {
            return;
        }

        let old_length_ = Length::Definite(old_length).to_bytes();
        let new_length_ = Length::Definite(new_length).to_bytes();

        unsafe {
            let mut dest = self.buffer.as_mut_ptr();

            // Copy the new_length octets
            let src = new_length_.as_ptr();
            dest = dest.add(id_len);
            src.copy_to(dest, new_length_.len());

            // Copy the contents octets if necessary.
            if new_length_.len() < old_length_.len() {
                let src = dest.add(old_length_.len()) as *const u8;
                dest = dest.add(new_length_.len());
                src.copy_to(dest, new_length);
            }

            let new_total_len = id_len + new_length_.len() + new_length;
            self.buffer.set_len(new_total_len);
        }
    }
}

pub fn disassemble_der(der: Der) -> Buffer {
    der.buffer
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = <&ContentsRef>::from(bytes);
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
            let expected = Der::new(id, <&ContentsRef>::from(&[]));
            assert_eq!(expected, der);
        }

        // Single slice of empty bytes.
        {
            let contents: &[&[u8]] = &[&[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, <&ContentsRef>::from(&[]));
            assert_eq!(expected, der);
        }

        // Single slice of not empty bytes.
        {
            let contents: &[&[u8]] = &[&[1, 2, 3]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, <&ContentsRef>::from(&[1, 2, 3]));
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // Both elements are empty.
        {
            let contents: &[&[u8]] = &[&[], &[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, <&ContentsRef>::from(&[]));
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // One of the elements is empty
        {
            let contents: &[&[u8]] = &[&[], &[1, 2]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, <&ContentsRef>::from(&[1, 2]));
            assert_eq!(expected, der);

            let contents: &[&[u8]] = &[&[3], &[]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, <&ContentsRef>::from(&[3]));
            assert_eq!(expected, der);
        }

        // 2 elements slice.
        // Neither element is empty
        {
            let contents: &[&[u8]] = &[&[1, 2], &[3]];
            let der = Der::from_id_iterator(id, contents.iter());
            let expected = Der::new(id, <&ContentsRef>::from(&[1, 2, 3]));
            assert_eq!(expected, der);
        }
    }

    #[test]
    fn from_bool() {
        for &b in &[false, true] {
            let der = Der::from(b);
            assert_eq!(IdRef::boolean(), der.id());
            assert_eq!(b, der.contents().to_bool_der().unwrap());
        }
    }

    #[test]
    fn from_i8() {
        for i in std::i8::MIN..=std::i8::MAX {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_u8() {
        for i in std::u8::MIN..=std::u8::MAX {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_i16() {
        for i in std::i16::MIN..=std::i16::MAX {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_u16() {
        for i in std::u16::MIN..=std::u16::MAX {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_i32() {
        let range = Some(i32::MIN)
            .into_iter()
            .chain(Some(i16::MIN as i32 - 1))
            .chain(i16::MIN as i32..=i16::MAX as i32)
            .chain(Some(i16::MAX as i32 + 1))
            .chain(Some(i32::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_u32() {
        let range = (0..=u16::MAX as u32)
            .chain(Some(u16::MAX as u32 + 1))
            .chain(Some(u32::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_i64() {
        let range = Some(i64::MIN)
            .into_iter()
            .chain(Some(i16::MIN as i64 - 1))
            .chain(i16::MIN as i64..=i16::MAX as i64)
            .chain(Some(i16::MAX as i64 + 1))
            .chain(Some(i64::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_u64() {
        let range = (0..=u16::MAX as u64)
            .chain(Some(u16::MAX as u64 + 1))
            .chain(Some(u64::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_i128() {
        let range = Some(i128::MIN)
            .into_iter()
            .chain(Some(i16::MIN as i128 - 1))
            .chain(i16::MIN as i128..=i16::MAX as i128)
            .chain(Some(i16::MAX as i128 + 1))
            .chain(Some(i128::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_u128() {
        let range = (0..=u16::MAX as u128)
            .chain(Some(u16::MAX as u128 + 1))
            .chain(Some(u128::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_isize() {
        let range = Some(isize::MIN)
            .into_iter()
            .chain(Some(i16::MIN as isize - 1))
            .chain(i16::MIN as isize..=i16::MAX as isize)
            .chain(Some(i16::MAX as isize + 1))
            .chain(Some(isize::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_usize() {
        let range = (0..=u16::MAX as usize)
            .chain(Some(u16::MAX as usize + 1))
            .chain(Some(usize::MAX));
        for i in range {
            let der = Der::from(i);
            assert_eq!(IdRef::integer(), der.id());
            assert_eq!(i, der.contents().to_integer().unwrap());
        }
    }

    #[test]
    fn from_str() {
        let val = "foo";
        let der = Der::from(val);
        assert_eq!(IdRef::utf8_string(), der.id());
        assert_eq!(val.as_bytes(), der.contents().as_ref());
    }

    #[test]
    fn parse() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = <&ContentsRef>::from(bytes);
            let der = Der::new(id, contents);
            let der_ref = DerRef::parse(der.as_ref()).unwrap();
            assert_eq!(der_ref, &der as &DerRef);
        }
    }

    #[test]
    fn extend_from_slice() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();

        for i in 0..bytes.len() {
            for j in 0..bytes.len() {
                let mut der = Der::from(&bytes[..i]);
                der.extend_from_slice(&bytes[..j]);

                assert_eq!(der.id(), IdRef::octet_string());
                assert_eq!(der.length(), Length::Definite(i + j));
                assert_eq!(&der.contents().as_ref()[..i], &bytes[..i]);
                assert_eq!(&der.contents().as_ref()[i..], &bytes[..j]);
            }
        }
    }

    #[test]
    fn truncate() {
        let contents: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..contents.len() {
            let mut der = Der::from(&contents[..]);

            der.truncate(i as usize);
            assert_eq!(der.id(), IdRef::octet_string());
            assert_eq!(der.length(), Length::Definite(i as usize));
            assert_eq!(der.contents().as_ref(), &contents[..i as usize]);
        }

        for &i in &[contents.len(), contents.len() + 1] {
            let mut der = Der::from(&contents[..]);
            der.truncate(i);

            der.truncate((der.as_ref() as &[u8]).len() + 1);
            assert_eq!(der.id(), IdRef::octet_string());
            assert_eq!(der.length(), Length::Definite(contents.len()));
            assert_eq!(der.contents().as_ref(), &contents[..]);
        }
    }
}
