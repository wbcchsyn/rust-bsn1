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
/// Users can access the inner [`BerRef`] via the `Deref` and `DerefMut` implementation.
///
/// # Warnings
///
/// ASN.1 allows BER both 'definite' and 'indefinite' length octets.
/// In case of 'indefinite', the contents must be a sequence of BERs,
/// and must be terminated by 'EOC BER'.
/// (Single 'EOC BER' is allowed.)
///
/// `Ber` instance works fine even if the user violates the rule,
/// however, the holding octets will be invalid as a BER then.
/// Such octets can not be parsed as a BER again.
#[derive(Debug, Clone, Eq, Hash)]
pub struct Ber {
    buffer: Buffer,
}

impl Ber {
    /// Creates a new instance with definite length from `id` and `contents`.
    ///
    /// Note that BER allows both definite length and indefinite length,
    /// however, this function always returns a definite length value.
    /// Use [`new_indefinite`] to build an indefinite length value.
    ///
    /// Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used,
    /// however, this function ignores the rule.
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
    /// let contents: &ContentsRef = "Foo".into();
    /// let ber = Ber::new(id, contents);
    ///
    /// assert_eq!(ber.id(), id);
    /// assert!(ber.length().is_definite());
    /// assert_eq!(ber.contents().as_ref(), "Foo".as_bytes());
    /// ```
    pub fn new(id: &IdRef, contents: &ContentsRef) -> Self {
        Der::new(id, contents).into()
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
    /// however, this function ignores the rule.
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
    /// use bsn1::{Ber, BerRef, Contents, ContentsRef, IdRef, Length};
    ///
    /// let id = IdRef::sequence();
    ///
    /// let contents0 = Ber::new(IdRef::utf8_string(), "Foo".as_bytes().into());
    /// let contents1 = Ber::new(IdRef::integer(), &Contents::from(29_i32));
    /// let contents2 = BerRef::eoc();
    ///
    /// let mut contents: Vec<u8> = Vec::new();
    /// contents.extend_from_slice(contents0.as_ref() as &[u8]);
    /// contents.extend_from_slice(contents1.as_ref() as &[u8]);
    /// contents.extend_from_slice(contents2.as_ref() as &[u8]);
    ///
    /// let ber = Ber::new_indefinite(id, contents.as_slice().into());
    ///
    /// assert_eq!(ber.id(), id);
    /// assert!(ber.length().is_indefinite());
    ///
    /// let mut contents_: &[u8] = ber.contents().as_ref();
    ///
    /// let contents0_ = BerRef::parse(&mut contents_).unwrap();
    /// assert_eq!(contents0, contents0_);
    ///
    /// let contents1_ = BerRef::parse(&mut contents_).unwrap();
    /// assert_eq!(contents1, contents1_);
    ///
    /// let contents2_ = BerRef::parse(&mut contents_).unwrap();
    /// assert_eq!(contents2, contents2_);
    ///
    /// assert_eq!(contents_.is_empty(), true);
    /// ```
    pub fn new_indefinite(id: &IdRef, contents: &ContentsRef) -> Self {
        let mut ret = Self::with_id_length_indefinite(id, contents.len());
        ret.mut_contents()
            .as_mut()
            .copy_from_slice(contents.as_ref());

        ret
    }

    /// Creates a new instance with `id` and 'definite `length`'.
    ///
    /// The 'contents octets' of the return value holds `length` bytes,
    /// but they are not initialized.
    /// Use [`mut_contents`] via `DerefMut` implementation to initialize them.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used, however, this
    /// function ignores the rule. For example, the number 15 (0x0f) is reserved for now,
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
    /// let mut ber = Ber::with_id_length(IdRef::utf8_string(), "Hello".len());
    ///
    /// assert_eq!(ber.id(), IdRef::utf8_string());
    /// assert_eq!(ber.length(), Length::Definite("Hello".len()));
    /// assert_eq!(ber.contents().len(), "Hello".len());
    ///
    /// ber.mut_contents().as_mut().copy_from_slice("Hello".as_bytes());
    /// assert_eq!(ber.contents().as_ref(), "Hello".as_bytes());
    /// ```
    pub fn with_id_length(id: &IdRef, length: usize) -> Self {
        Der::with_id_length(id, length).into()
    }

    /// Creates a new instance with `id` and 'indefinite length'.
    ///
    /// The 'contents octets' of the return value holds `length` bytes,
    /// but they are not initialized.
    /// Use [`mut_contents`] via `DerefMut` implementation to initialize them.
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
    /// let mut ber = Ber::with_id_length_indefinite(IdRef::utf8_string(), "Hello".len());
    ///
    /// assert_eq!(ber.id(), IdRef::utf8_string());
    /// assert!(ber.length().is_indefinite());
    /// assert_eq!(ber.contents().len(), "Hello".len());
    ///
    /// ber.mut_contents().as_mut().copy_from_slice("Hello".as_bytes());
    /// assert_eq!(ber.contents().as_ref(), "Hello".as_bytes());
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
    /// On error, the state of `readable` is unspecified;
    /// otherwise, `readable` is advanced to the end of BER octets.
    ///
    /// # Performance
    ///
    /// This function is not so efficient compared with [`Ber::parse`].
    /// If you have a slice of serialized BER, use [`BerRef::parse`]
    /// and then call `Ber::from` instead.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifiers and they should not be used, however, this
    /// function ignores the rule. For example, the number 15 (0x0f) is reserved for now,
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
    /// // Deserialize.
    /// {
    ///     let serialized = &mut &serialized[..];
    ///     let deserialized = Ber::parse(serialized).unwrap();
    ///     assert_eq!(ber, deserialized);
    ///     assert!(serialized.is_empty());
    /// }
    ///
    /// // Extra octets at the end does not affect the result.
    /// serialized.push(0x00);
    /// serialized.push(0x01);
    /// {
    ///     let serialized = &mut &serialized[..];
    ///     let deserialized = Ber::parse(serialized).unwrap();
    ///     assert_eq!(ber, deserialized);
    ///     assert_eq!(serialized, &[0x00, 0x01]);
    /// }
    ///
    /// // We can access to the inner slice of `serialized`.
    /// // We can use `BerRef::parse` instead of this function.
    /// // (`BerRef::parse` is more efficient than this function.)
    /// let deserialized: Ber = BerRef::parse(&mut &serialized[..]).unwrap().into();
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

                let buffer = &mut writeable.as_mut_slice()[current_len..];
                readable.read_exact(buffer).map_err(Error::from)?;

                let read = &(writeable.as_slice()[init_len..]);
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
    /// let ber = Ber::from(5_i32);
    /// let serialized: &[u8] = ber.as_ref();
    /// let deserialized = unsafe { Ber::from_bytes_unchecked(serialized) };
    /// assert_eq!(ber, deserialized);
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
    /// let ber = Ber::from(5_i32);
    /// let serialized = ber.clone().into_vec();
    /// let from_vec = unsafe { Ber::from_vec_unchecked(serialized) };
    ///
    /// assert_eq!(ber, from_vec);
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

    /// Consumes `self`, returning `Vec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, Contents, IdRef};
    ///
    /// let id = IdRef::octet_string();
    /// let contents = Contents::from(&[0, 1, 2, 3, 4]);
    ///
    /// let ber = Ber::new(id, &contents);
    /// let v = ber.clone().into_vec();
    ///
    /// assert_eq!(ber.as_ref() as &[u8], &v);
    /// ```
    pub fn into_vec(self) -> Vec<u8> {
        self.buffer.into_vec()
    }

    /// Appends `byte` to the end of the 'contents octets'.
    ///
    /// If `self` had indefinite length, the length octets will not be changed;
    /// otherwise, the length octets will be `Length::Definite(new_length)`
    /// where `new_length` is the current byte count of the 'contents octets' plus 1.
    ///
    /// Note that this method may shift the 'contents octets',
    /// and the performance is `O(n)` where `n` is the byte count of 'contents octets'
    /// in the worst-case,
    /// because the byte count of 'length octets' may change.
    /// (BER is composed of 'identifier octets', 'length octets' and 'contents octets'
    /// in this order.)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef, Length};
    ///
    /// let bytes: Vec<u8> = (0..10).collect();
    ///
    /// // Push to BER with definite length.
    /// let mut ber = Ber::from(&bytes[..9]);
    /// ber.push(bytes[9]);
    ///
    /// assert_eq!(ber.id(), IdRef::octet_string());
    /// assert_eq!(ber.length(), Length::Definite(bytes.len()));
    /// assert_eq!(ber.contents().as_ref(), &bytes[..]);
    ///
    /// // Push to BER with indefinite length.
    /// let mut ber = Ber::new_indefinite(IdRef::octet_string(), (&bytes[..9]).into());
    /// ber.push(bytes[9]);
    ///
    /// assert_eq!(ber.id(), IdRef::octet_string());
    /// assert!(ber.length().is_indefinite());
    ///
    /// assert_eq!(ber.contents().as_ref(), &bytes[..]);
    /// ```
    pub fn push(&mut self, byte: u8) {
        self.extend_from_slice(&[byte]);
    }

    /// Appends `bytes` to the end of the 'contents octets'.
    ///
    /// If `self` had indefinite length, the length octets will not be changed;
    /// otherwise, the length octets will be `Length::Definite(new_length)`
    /// where `new_length` is the current byte count of the 'contents octets' plus `bytes.len()`.
    ///
    /// Note that this method may shift the 'contents octets',
    /// and the performance is `O(n)` where `n` is the byte count of 'contents octets'
    /// in the worst-case,
    /// because the byte count of 'length octets' may change.
    /// (BER is composed of 'identifier octets', 'length octets' and 'contents octets'
    /// in this order.)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, IdRef, Length};
    ///
    /// let bytes: Vec<u8> = (0..10).collect();
    ///
    /// // Extends BER with definite length.
    /// let mut ber = Ber::from(&bytes[..5]);
    /// ber.extend_from_slice(&bytes[5..]);
    ///
    /// assert_eq!(ber.id(), IdRef::octet_string());
    /// assert_eq!(ber.length(), Length::Definite(bytes.len()));
    /// assert_eq!(ber.contents().as_ref(), &bytes[..]);
    ///
    /// // Extends BER with indefinite length.
    /// let mut ber = Ber::new_indefinite(IdRef::octet_string(), (&bytes[..5]).into());
    /// ber.extend_from_slice(&bytes[5..]);
    ///
    /// assert_eq!(ber.id(), IdRef::octet_string());
    /// assert!(ber.length().is_indefinite());
    /// assert_eq!(ber.contents().as_ref(), &bytes[..]);
    /// ```
    pub fn extend_from_slice<T>(&mut self, bytes: &T)
    where
        T: ?Sized + AsRef<[u8]>,
    {
        let bytes = bytes.as_ref();

        match self.length() {
            Length::Definite(_) => unsafe {
                let this = std::mem::transmute::<&mut Self, &mut Der>(self);
                this.extend_from_slice(bytes);
            },
            Length::Indefinite => {
                self.buffer.reserve(bytes.len());

                let src = bytes.as_ptr();
                let dst = unsafe { self.buffer.as_mut_ptr().add(self.buffer.len()) };
                unsafe {
                    src.copy_to_nonoverlapping(dst, bytes.len());
                    self.buffer.set_len(self.buffer.len() + bytes.len());
                }
            }
        }
    }

    /// Enshorten the `contents`, keeping the first `new_length` and discarding the rest
    /// if `new_length` is less than the length of the current 'contents octets';
    /// otherwise, does nothing.
    ///
    /// If `self` had indefinite length, the length octets will not be changed;
    /// otherwise, the length octets will be `Length::Definite(new_length)`
    /// if `new_length` is less than the current byte count of the 'contents octets'.
    ///
    /// Note that this method may shift the 'contents octets',
    /// and the performance is `O(n)` where `n` is the byte count of 'contents octets'
    /// in the worst-case,
    /// because the byte count of 'length octets' may change.
    /// (BER is composed of 'identifier octets', 'length octets' and 'contents octets'
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
    /// use bsn1::{Ber, IdRef, Length};
    ///
    /// let bytes: Vec<u8> = (0..=255).collect();
    ///
    /// // Truncate BER with definite length.
    /// let mut ber = Ber::from(&bytes[..]);
    /// ber.truncate(100);
    ///
    /// assert_eq!(ber.id(), IdRef::octet_string());
    /// assert_eq!(ber.length(), Length::Definite(100));
    /// assert_eq!(ber.contents().as_ref(), &bytes[..100]);
    ///
    /// // Truncate BER with indefinite length.
    /// let mut ber = Ber::new_indefinite(IdRef::octet_string(), (&bytes[..]).into());
    /// ber.truncate(100);
    ///
    /// assert_eq!(ber.id(), IdRef::octet_string());
    /// assert!(ber.length().is_indefinite());
    /// assert_eq!(ber.contents().as_ref(), &bytes[..100]);
    /// ```
    pub fn truncate(&mut self, new_length: usize) {
        match self.length() {
            Length::Definite(_) => unsafe {
                let this = std::mem::transmute::<&mut Self, &mut Der>(self);
                this.truncate(new_length);
            },
            Length::Indefinite => {
                let old_length = self.contents().len();
                if old_length <= new_length {
                    return;
                } else {
                    let new_total_len = self.buffer.len() + new_length - old_length;
                    unsafe { self.buffer.set_len(new_total_len) };
                }
            }
        }
    }
}

#[doc(hidden)]
impl From<Buffer> for Ber {
    fn from(buffer: Buffer) -> Self {
        Self { buffer }
    }
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

impl AsRef<[u8]> for Ber {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_slice()
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
        unsafe { BerRef::from_bytes_unchecked(self.buffer.as_slice()) }
    }
}

impl DerefMut for Ber {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { BerRef::from_mut_bytes_unchecked(self.buffer.as_mut_slice()) }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_deinite() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let ber = Ber::from(&bytes[..i]);
            let mut bytes: &[u8] = ber.as_ref();
            let parsed = Ber::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_indefinite() {
        let bers: Vec<Ber> = (0..10).map(Ber::from).collect();

        for i in 0..10 {
            let contents: Vec<u8> = bers[..i]
                .iter()
                .map(|ber| ber.as_ref() as &[u8])
                .flatten()
                .copied()
                .collect();
            let mut ber = Ber::new_indefinite(IdRef::sequence(), contents.as_slice().into());
            ber.extend_from_slice(BerRef::eoc());

            let mut bytes: &[u8] = ber.as_ref();
            let parsed = Ber::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_deinite_in_definite() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let inner = Ber::from(&bytes[..i]);

            let ber = Ber::new(IdRef::sequence(), (inner.as_ref() as &[u8]).into());
            let mut bytes: &[u8] = ber.as_ref();

            let parsed = Ber::parse(&mut bytes).unwrap();
            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_indeinite_in_definite() {
        let bers: Vec<Ber> = (0..10).map(Ber::from).collect();
        for i in 0..bers.len() {
            let contents: Vec<u8> = bers[..i]
                .iter()
                .map(|ber| ber.as_ref() as &[u8])
                .flatten()
                .copied()
                .collect();
            let mut inner = Ber::new_indefinite(IdRef::octet_string(), contents.as_slice().into());
            inner.extend_from_slice(BerRef::eoc());

            let ber = Ber::new(IdRef::sequence(), (inner.as_ref() as &[u8]).into());
            let mut bytes: &[u8] = ber.as_ref();

            let parsed = Ber::parse(&mut bytes).unwrap();
            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_deinite_in_indefinite() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let inner = Ber::from(&bytes[..i]);

            let mut ber = Ber::new_indefinite(IdRef::sequence(), (inner.as_ref() as &[u8]).into());
            ber.extend_from_slice(BerRef::eoc());

            let mut bytes: &[u8] = ber.as_ref();
            let parsed = Ber::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_indeinite_in_indefinite() {
        let bers: Vec<Ber> = (0..10).map(Ber::from).collect();
        for i in 0..bers.len() {
            let contents: Vec<u8> = bers[..i]
                .iter()
                .map(|ber| ber.as_ref() as &[u8])
                .flatten()
                .copied()
                .collect();
            let mut inner = Ber::new_indefinite(IdRef::octet_string(), contents.as_slice().into());
            inner.extend_from_slice(BerRef::eoc());

            let mut ber = Ber::new_indefinite(IdRef::sequence(), (inner.as_ref() as &[u8]).into());
            ber.extend_from_slice(BerRef::eoc());

            let mut bytes: &[u8] = ber.as_ref();
            let parsed = Ber::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn truncate_definite() {
        let contents: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..contents.len() {
            let mut ber = Ber::from(&contents[..]);

            ber.truncate(i as usize);
            assert_eq!(ber.id(), IdRef::octet_string());
            assert_eq!(ber.length(), Length::Definite(i as usize));
            assert_eq!(ber.contents().as_ref(), &contents[..i as usize]);
        }

        for &i in &[contents.len(), contents.len() + 1] {
            let mut ber = Ber::from(&contents[..]);
            ber.truncate(i);

            ber.truncate((ber.as_ref() as &[u8]).len() + 1);
            assert_eq!(ber.id(), IdRef::octet_string());
            assert_eq!(ber.length(), Length::Definite(contents.len()));
            assert_eq!(ber.contents().as_ref(), &contents[..]);
        }
    }

    #[test]
    fn truncate_indefinite() {
        let contents: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..contents.len() {
            let mut ber = Ber::new_indefinite(IdRef::octet_string(), (&contents[..]).into());

            ber.truncate(i as usize);
            assert_eq!(ber.id(), IdRef::octet_string());
            assert!(ber.length().is_indefinite());
            assert_eq!(ber.contents().as_ref(), &contents[..i as usize]);
        }

        for &i in &[contents.len(), contents.len() + 1] {
            let mut ber = Ber::new_indefinite(IdRef::octet_string(), (&contents[..]).into());
            ber.truncate(i);

            ber.truncate((ber.as_ref() as &[u8]).len() + 1);
            assert_eq!(ber.id(), IdRef::octet_string());
            assert!(ber.length().is_indefinite());
            assert_eq!(ber.contents().as_ref(), &contents[..]);
        }
    }

    #[test]
    fn extend_definite_from_slice() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();

        for i in 0..bytes.len() {
            for j in 0..bytes.len() {
                let mut ber = Ber::from(&bytes[..i]);
                ber.extend_from_slice(&bytes[..j]);

                assert_eq!(ber.id(), IdRef::octet_string());
                assert_eq!(ber.length(), Length::Definite(i + j));
                assert_eq!(&ber.contents().as_ref()[..i], &bytes[..i]);
                assert_eq!(&ber.contents().as_ref()[i..], &bytes[..j]);
            }
        }
    }

    #[test]
    fn extend_indefinite_from_slice() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();

        for i in 0..bytes.len() {
            for j in 0..bytes.len() {
                let mut ber = Ber::new_indefinite(IdRef::octet_string(), (&bytes[..i]).into());
                ber.extend_from_slice(&bytes[..j]);

                assert_eq!(ber.id(), IdRef::octet_string());
                assert!(ber.length().is_indefinite());
                assert_eq!(&ber.contents().as_ref()[..i], &bytes[..i]);
                assert_eq!(&ber.contents().as_ref()[i..], &bytes[..j]);
            }
        }
    }
}
