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
use num::PrimInt;
use std::borrow::Borrow;
use std::convert::TryFrom;
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

impl TryFrom<&[u8]> for Ber {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`try_from_bytes`].
    ///
    /// [`try_from_bytes`]: Ber::try_from_bytes
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let ber_ref = <&BerRef>::try_from(bytes)?;
        Ok(ber_ref.to_owned())
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
            ptr.copy_from_nonoverlapping(id.as_bytes().as_ptr(), id.len());

            let ptr = ptr.add(id.len());
            ptr.copy_from_nonoverlapping(length.as_ptr(), length.len());

            let ptr = ptr.add(length.len());
            ptr.copy_from_nonoverlapping(contents.as_bytes().as_ptr(), contents.len());
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
            dst.copy_from_nonoverlapping(id.as_bytes().as_ptr(), id.len());

            let dst = dst.add(id.len());
            dst.copy_from_nonoverlapping(length_.as_ptr(), length_.len());

            buffer.set_len(total_len);
        }

        Self { buffer }
    }

    /// Parses `bytes` starting with BER octets and returns a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// This function is the same as [`TryFrom::try_from`].
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used, however, this
    /// function accepts such identifiers. For example, the number 15 (0x0f) is reserved for now,
    /// but this function returns `Ok`.
    ///
    /// [`TryFrom::try_from`]: #method.try_from
    pub fn try_from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::try_from(bytes)
    }

    /// Returns a new instance holding `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as a 'BER', use [`TryFrom`]
    /// implementation or [`try_from_bytes`] instead.
    ///
    /// [`TryFrom`]: #method.try_from
    /// [`try_from_bytes`]: Self::try_from_bytes
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
    /// let ber1 = unsafe { Ber::from_bytes_unchecked(ber0.as_bytes()) };
    /// assert_eq!(ber0, ber1);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }

    /// Creates a new instance from `id` and `contents`.
    ///
    /// The all length octets will be `definite`.
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
    /// let id = IdRef::sequence();
    ///
    /// // Builds an instance using function 'from_id_iterator()'.
    /// let contents: &[Ber] = &[Ber::utf8_string("foo"), Ber::integer(29_i32)];
    /// let ber = Ber::from_id_iterator(id, contents.iter());
    ///
    /// // Builds an instance using function 'new()'.
    /// let contents: Vec<u8> = contents.iter()
    ///                         .map(|i| Vec::from(i.as_bytes()))
    ///                         .flatten().collect();
    /// let contents = <&ContentsRef>::from(&contents as &[u8]);
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
    /// Type `T` should be a built-in primitive integer type (e.g., u8, u32, isize, i128, ...)
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
    /// # Panics
    ///
    /// Panics if the total length exceeds `isize::MAX`.
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
    /// assert_eq!(val.as_bytes(), ber.contents().as_bytes());
    /// ```
    pub fn utf8_string(val: &str) -> Self {
        Self::from(Der::utf8_string(val))
    }

    /// Returns a new instance representing an octet_string.
    ///
    /// # Panics
    ///
    /// Panics if the total length exceeds `isize::MAX`.
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
    /// assert_eq!(val, ber.contents().as_bytes());
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
    /// assert_eq!(ber.as_bytes(), &v);
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
    /// let mut ber = Ber::new(IdRef::octet_string(), <&ContentsRef>::from(old_contents));
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_from_deinite() {
        let id = IdRef::octet_string();

        let byteses: &[&[u8]] = &[&[], &[0x00], &[0xff], &[0x00, 0x00], &[0xff, 0xff]];
        for &bytes in byteses {
            let contents = <&ContentsRef>::from(bytes);
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
