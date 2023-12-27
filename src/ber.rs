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

use crate::{BerRef, Buffer, ContentsRef, Der, DerRef, Error, IdRef, Length};
use std::borrow::Borrow;
use std::io::Read;
use std::ops::{Deref, DerefMut};

/// `Ber` owns [`BerRef`] and represents a BER.
///
/// The structure of `Ber` is similar to that of `Vec<u8>`.
///
/// Users can access the [`BerRef`] via the [`Deref`] and [`DerefMut`] implementation
/// and the inner slice via the [`BerRef`].
#[derive(Debug, Clone, Eq, Hash)]
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

impl From<bool> for Ber {
    /// Creates a new instance representing a boolean containing `contents`.
    fn from(contents: bool) -> Self {
        Der::from(contents).into()
    }
}

impl From<i8> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: i8) -> Self {
        Der::from(contents).into()
    }
}

impl From<u8> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: u8) -> Self {
        Der::from(contents).into()
    }
}

impl From<i16> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: i16) -> Self {
        Der::from(contents).into()
    }
}

impl From<u16> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: u16) -> Self {
        Der::from(contents).into()
    }
}

impl From<i32> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: i32) -> Self {
        Der::from(contents).into()
    }
}

impl From<u32> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: u32) -> Self {
        Der::from(contents).into()
    }
}

impl From<i64> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: i64) -> Self {
        Der::from(contents).into()
    }
}

impl From<u64> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: u64) -> Self {
        Der::from(contents).into()
    }
}

impl From<i128> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: i128) -> Self {
        Der::from(contents).into()
    }
}

impl From<u128> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: u128) -> Self {
        Der::from(contents).into()
    }
}

impl From<isize> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: isize) -> Self {
        Der::from(contents).into()
    }
}

impl From<usize> for Ber {
    /// Creates a new instance representing a integer containing `contents`.
    fn from(contents: usize) -> Self {
        Der::from(contents).into()
    }
}

impl From<&str> for Ber {
    /// Creates a new instance representing a utf8-string containing `contents`.
    fn from(contents: &str) -> Self {
        Der::from(contents).into()
    }
}

impl From<&[u8]> for Ber {
    /// Creates a new instance representing an octet-string containing `contents`.
    fn from(contents: &[u8]) -> Self {
        Der::from(contents).into()
    }
}

impl Ber {
    /// Creates a new instance from `id` and `contents` with definite length.
    ///
    /// Note that BER allows both definite length and indefinite length,
    /// however, this function always returns a definite length value.
    /// Use [`new_indefinite`] to build an indefinite length value.
    ///
    /// Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used,
    /// however, this function accepts such identifiers.
    /// For example, the number 15 (0x0f) is reserved for now, but this function creates such
    /// an instance with the number 15 identifier.
    ///
    /// # Panics
    ///
    /// Panics if the total length exceeds `isize::MAX`.
    ///
    /// [`new_indefinite`]: Self::new_indefinite
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = <&ContentsRef>::from(&[]);
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
    /// Note that BER allows both definite length and indefinite length,
    /// however, this function always returns an indefinite length value.
    /// Use [`new`] to build a definite length value.
    ///
    /// Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used,
    /// however, this function accepts such identifiers.
    /// For example, the number 15 (0x0f) is reserved for now, but this function creates such
    /// an instance with the number 15 identifier.
    ///
    /// # Panics
    ///
    /// Panics if the total length exceeds `isize::MAX`.
    ///
    /// [`new`]: Self::new
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef, Length};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = <&ContentsRef>::from(&[]);
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
            ptr.copy_from_nonoverlapping(id.as_ref().as_ptr(), id.len());

            let ptr = ptr.add(id.len());
            ptr.copy_from_nonoverlapping(length.as_ptr(), length.len());

            let ptr = ptr.add(length.len());
            ptr.copy_from_nonoverlapping(contents.as_ref().as_ptr(), contents.len());
        }

        Self { buffer }
    }

    /// Creates a new instance with definite length from `id` and `contents` of `length` bytes.
    ///
    /// The `contents` of the return value are not initialized.
    /// Use [`mut_contents`] via [`DerefMut`] implementation to initialize it.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used, however, this
    /// function accepts such identifiers. For example, the number 15 (0x0f) is reserved for now,
    /// but this function creates such an instance with the number 15 identifier.
    ///
    /// # Panics
    ///
    /// Panics if the total bytes exceeds `isize::MAX`.
    ///
    /// [`mut_contents`]: BerRef::mut_contents
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
    /// The `contents` of the return value are not initialized.
    /// Use [`mut_contents`] via [`DerefMut`] implementation to initialize it.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used, however, this
    /// function accepts such identifiers. For example, the number 15 (0x0f) is reserved for now,
    /// but this function creates such an instance with the number 15 identifier.
    ///
    /// # Panics
    ///
    /// Panics if the total bytes exceeds `isize::MAX`.
    ///
    /// [`mut_contents`]: BerRef::mut_contents
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
            dst.copy_from_nonoverlapping(id.as_ref().as_ptr(), id.len());

            let dst = dst.add(id.len());
            dst.copy_from_nonoverlapping(length_.as_ptr(), length_.len());

            buffer.set_len(total_len);
        }

        Self { buffer }
    }

    /// Parses `readable` starting with BER octets and returns a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// # Performance
    ///
    /// This function is not so efficient compared with [`Ber::parse`].
    /// If you have a slice of serialized BER, use [`BerRef::parse`]
    /// and then call [`ToOwned::to_owned`] instead.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used, however, this
    /// function accepts such identifiers. For example, the number 15 (0x0f) is reserved for now,
    /// but this function returns `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef};
    ///
    /// // Serialize DER of '10' as Integer.
    /// let ber = Ber::from(10_i32);
    /// let mut serialized = Vec::from(ber.as_ref() as &[u8]);
    ///
    /// // Deserialize it.
    /// let deserialized = Ber::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(ber, deserialized);
    ///
    /// // Extra octets at the end does not affect the result.
    /// serialized.push(0x00);
    /// serialized.push(0x01);
    /// let deserialized = Ber::parse(&mut &serialized[..]).unwrap();
    ///
    /// assert_eq!(ber, deserialized);
    ///
    /// // We can access to the inner slice of `serialized`.
    /// // We can use `BerRef::parse` instead of this function.
    /// // (`BerRef::parse` is more efficient than this function.)
    /// let deserialized = BerRef::parse(&serialized[..]).map(ToOwned::to_owned).unwrap();
    /// assert_eq!(ber, deserialized);
    /// ```
    pub fn parse<R: Read>(readable: &mut R) -> Result<Self, Error> {
        let mut buffer = Buffer::new();
        let mut stack_depth: isize = 0;

        while {
            stack_depth += Self::do_parse(readable, &mut buffer)? as isize;
            stack_depth > 0
        } {}

        Ok(Self { buffer })
    }

    fn do_parse<R: Read>(readable: &mut R, writeable: &mut Buffer) -> Result<i8, Error> {
        let init_len = writeable.len();

        match unsafe { crate::misc::parse_id_length(readable, writeable)? } {
            Length::Definite(length) => {
                writeable.reserve(length);
                let current_len = writeable.len();
                unsafe { writeable.set_len(current_len + length) };

                let buffer = &mut writeable.as_mut_bytes()[current_len..];
                readable.read_exact(buffer).map_err(Error::from)?;

                let read = &(writeable.as_bytes()[init_len..]);
                if read == BerRef::eoc().as_ref() {
                    Ok(-1)
                } else {
                    Ok(0)
                }
            }
            Length::Indefinite => Ok(1),
        }
    }

    /// Returns a new instance holding `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as a 'BER', use [`parse`] instead.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a BER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let contents = <&ContentsRef>::from(&[]);
    /// let ber0 = Ber::new(IdRef::octet_string(), contents);
    /// let ber1 = unsafe { Ber::from_bytes_unchecked(ber0.as_ref()) };
    /// assert_eq!(ber0, ber1);
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
    /// The behavior is undefined if `bytes` is not formatted as a BER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::Ber;
    ///
    /// let ber0 = Ber::from(5_i32);
    /// let bytes = ber0.clone().into_vec();
    /// let ber1 = unsafe { Ber::from_vec_unchecked(bytes) };
    ///
    /// assert_eq!(ber0, ber1);
    /// ```
    pub unsafe fn from_vec_unchecked(bytes: Vec<u8>) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Creates a new instance containing concatnated `contents`.
    ///
    /// The length octets will be `definite`.
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
    /// // Build an sequence DER containing 2 other DERs.
    /// let contents0 = vec![Ber::from("foo"), Ber::from(29_i32)];
    /// let ber0 = Ber::from_id_iterator(IdRef::sequence(), contents0.iter());
    ///
    /// let mut contents1: Vec<u8> = Ber::from("foo").into_vec();
    /// contents1.extend_from_slice(&Ber::from(29_i32).into_vec());
    /// let ber1 = Ber::new(IdRef::sequence(), <&ContentsRef>::from(&contents1[..]));
    ///
    /// assert_eq!(ber0, ber1);
    ///
    /// // Build an utf8-string DER using function `from_id_iterator()`.
    /// let contents = vec!["Foo", "Bar"];
    /// let ber = Ber::from_id_iterator(
    ///             IdRef::utf8_string(), contents.iter().map(|s| s.as_bytes()));
    /// assert_eq!(ber, Ber::from("FooBar"));
    /// ```
    pub fn from_id_iterator<I>(id: &IdRef, contents: I) -> Self
    where
        I: Iterator + Clone,
        I::Item: AsRef<[u8]>,
    {
        let der = Der::from_id_iterator(id, contents);
        Self::from(der)
    }
}

impl AsRef<[u8]> for Ber {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_bytes()
    }
}

impl AsRef<BerRef> for Ber {
    fn as_ref(&self) -> &BerRef {
        self.deref()
    }
}

impl AsMut<BerRef> for Ber {
    fn as_mut(&mut self) -> &mut BerRef {
        self.deref_mut()
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

impl<T> PartialEq<T> for Ber
where
    T: Borrow<BerRef>,
{
    fn eq(&self, other: &T) -> bool {
        self.deref() == other.borrow()
    }
}

impl Ber {
    /// Consumes `self`, returning `Vec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = <&ContentsRef>::from(&[0, 1, 2, 3, 4]);
    ///
    /// let ber = Ber::new(id, contents);
    /// let v = ber.clone().into_vec();
    ///
    /// assert_eq!(ber.as_ref() as &[u8], &v);
    /// ```
    pub fn into_vec(self) -> Vec<u8> {
        self.buffer.into_vec()
    }

    /// Forces the length of the contents to `new_length`.
    ///
    /// If `new_length` is less than the current length of the `contents`, this method truncates
    /// the contents; otherwise, the `contents` is enlarged.
    /// The extended octets are not initialized. Use [`mut_contents`] via the [`Deref`]
    /// implementation to initialize them.
    ///
    /// If the contents length of `self` forms indefinite, the length octets is not changed;
    /// otherwise, the length octets will be updated.
    ///
    /// # Warnings
    ///
    /// `new_length` specifies the length of the contents.
    /// The total length of `self` will be greater than `new_length`.
    ///
    /// # Panics
    ///
    /// Panics if the new total length exceeds `isize::MAX`.
    ///
    /// [`mut_contents`]: BerRef::mut_contents
    ///
    /// # Examples
    ///
    /// Enlarge indefinite length Ber object.
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef, Length};
    ///
    /// let mut ber = Ber::new_indefinite(IdRef::octet_string(), <&ContentsRef>::from(&[]));
    ///
    /// assert_eq!(ber.length().is_indefinite(), true);
    /// assert_eq!(ber.contents().as_ref(), &[]);
    ///
    /// let new_contents: &[u8] = &[0, 1,  2, 3];
    /// ber.set_length(new_contents.len());
    /// ber.mut_contents().as_mut().clone_from_slice(new_contents);
    ///
    /// assert_eq!(ber.length().is_indefinite(), true);
    /// assert_eq!(ber.contents().as_ref(), new_contents);
    /// ```
    ///
    /// Enshorten definite length Ber object.
    ///
    /// ```
    /// use bsn1::{Ber, ContentsRef, IdRef, Length};
    ///
    /// let old_contents: &[u8] = &[0, 1, 2, 3, 4];
    /// let mut ber = Ber::new(IdRef::octet_string(), <&ContentsRef>::from(old_contents));
    ///
    /// assert_eq!(ber.length(), Length::Definite(old_contents.len()));
    /// assert_eq!(ber.contents().as_ref(), old_contents);
    ///
    /// let new_contents = &old_contents[0..2];
    /// ber.set_length(new_contents.len());
    /// ber.mut_contents().as_mut().clone_from_slice(new_contents);
    ///
    /// assert_eq!(ber.length(), Length::Definite(new_contents.len()));
    /// assert_eq!(ber.contents().as_ref(), new_contents);
    /// ```
    pub fn set_length(&mut self, new_length: usize) {
        match self.length() {
            Length::Indefinite => {
                let old_length = self.contents().len();

                let diff = (new_length as isize) - (old_length as isize);

                if 0 < diff {
                    self.buffer.reserve(diff as usize);
                }

                let total_len = (self.as_ref() as &[u8]).len() as isize + diff;
                unsafe { self.buffer.set_len(total_len as usize) };
            }
            _ => {
                let this: &mut Der = unsafe { std::mem::transmute(self) };
                this.set_length(new_length);
            }
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_deinite() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = <&ContentsRef>::from(bytes);
            let ber = Ber::new(id, contents);
            let ber_ref = BerRef::parse(ber.as_ref()).unwrap();
            assert_eq!(ber_ref, &ber as &BerRef);
        }
    }

    #[test]
    fn parse_indefinite() {
        let eoc = {
            let id = IdRef::eoc();
            let contents: &[u8] = &[];
            let contents = <&ContentsRef>::from(contents);
            Ber::new(id, contents)
        };

        let bers: Vec<Ber> = (0..10)
            .map(|i| {
                let id = IdRef::octet_string();
                let contents: &[u8] = &[i];
                let contents = <&ContentsRef>::from(contents);
                Ber::new(id, contents)
            })
            .collect();

        for i in 0..10 {
            let id = IdRef::sequence();
            let mut bytes: Vec<u8> = Vec::from(id.as_ref());

            bytes.extend(Length::Indefinite.to_bytes().iter());

            for ber in bers[0..i].iter() {
                bytes.extend(ber.as_ref() as &[u8]);
            }
            bytes.extend(eoc.as_ref() as &[u8]);

            let ber = BerRef::parse(&bytes[..]).unwrap();
            assert_eq!(&bytes, ber.as_ref());
        }
    }

    #[test]
    fn extend_indefinite_ber() {
        let mut ber = Ber::new_indefinite(IdRef::octet_string(), <&ContentsRef>::from(&[]));

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
            ber.set_length(256_usize.pow(3) - 1);
            assert_eq!(ber.length().is_indefinite(), true);

            let contents = ber.contents();
            assert_eq!(contents.len(), 256_usize.pow(3) - 1);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(256_usize.pow(3));
            assert_eq!(ber.length().is_indefinite(), true);

            let contents = ber.contents();
            assert_eq!(contents.len(), 256_usize.pow(3));
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }
    }

    #[test]
    fn extend_definite_ber() {
        let mut ber = Ber::new(IdRef::octet_string(), <&ContentsRef>::from(&[]));

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
            ber.set_length(256_usize.pow(3) - 1);
            assert_eq!(ber.length(), Length::Definite(256_usize.pow(3) - 1));

            let contents = ber.contents();
            assert_eq!(contents.len(), 256_usize.pow(3) - 1);
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }

        {
            ber.set_length(256_usize.pow(3));
            assert_eq!(ber.length(), Length::Definite(256_usize.pow(3)));

            let contents = ber.contents();
            assert_eq!(contents.len(), 256_usize.pow(3));
            for i in 0..=256 {
                assert_eq!(contents[i], i as u8);
            }
        }
    }

    #[test]
    fn enshorten_indefinite_der() {
        let contents: Vec<u8> = (0..=255).cycle().take(65537).collect();
        let mut ber = Ber::new_indefinite(
            IdRef::octet_string(),
            <&ContentsRef>::from(&contents as &[u8]),
        );

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
        let mut ber = Ber::new(
            IdRef::octet_string(),
            <&ContentsRef>::from(&contents as &[u8]),
        );

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
