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

use crate::{identifier, length, Buffer, Error, IdRef, Length};
use core::convert::TryFrom;
use core::ops::Deref;
use std::borrow::Borrow;

/// `DerRef` represents 'DER' octets in 'ASN.1.'
///
/// This struct is 'Unsized', so usually user uses a reference to the instance.
#[derive(Debug, PartialEq, Eq)]
pub struct DerRef {
    bytes: [u8],
}

impl<'a> TryFrom<&'a [u8]> for &'a DerRef {
    type Error = Error;

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a reference to `DerRef` .
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
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
    /// Provides a reference from `bytes` without any sanitization.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a 'DER'.
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        let ptr = bytes as *const [u8];
        let ptr = ptr as *const Self;
        &*ptr
    }

    /// Provides a reference from `bytes` that starts with an 'ASN.1 DER' octets.
    ///
    /// `bytes` may include some extra octet(s) at the end.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` does not start with 'ASN.1 DER' octets.
    pub unsafe fn from_bytes_starts_with_unchecked(bytes: &[u8]) -> &Self {
        let id = identifier::shrink_to_fit_unchecked(bytes);
        let parsing = &bytes[id.len()..];

        let (len, parsing) = match length::try_from(parsing).unwrap() {
            (Length::Definite(len), parsing) => (len, parsing),
            _ => panic!(format!("{}", Error::IndefiniteLength)),
        };

        let total_len = bytes.len() - parsing.len() + len;
        let bytes = &bytes[..total_len];
        Self::from_bytes_unchecked(bytes)
    }
}

impl AsRef<[u8]> for DerRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl Borrow<[u8]> for DerRef {
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

impl DerRef {
    /// Returns a reference to `IdRef` of `self` .
    pub fn id(&self) -> &IdRef {
        unsafe {
            let bytes = identifier::shrink_to_fit_unchecked(&self.bytes);
            IdRef::from_bytes_unchecked(bytes)
        }
    }

    /// Returns a `Length` to represent the length of contents.
    ///
    /// Note that 'DER' does not allow 'Indefinite Length.'
    /// The return value must be `Length::Definite` .
    pub fn length(&self) -> Length {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        length::try_from(bytes).unwrap().0
    }

    /// Returns a reference to 'contents octets' of `self` .
    pub fn contents(&self) -> &[u8] {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        length::try_from(bytes).unwrap().1
    }
}

/// `Der` owns `DerRef` and represents 'DER' octets in 'ASN.1.'
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

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and builds a new instance.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let der_ref = <&DerRef>::try_from(bytes)?;
        Ok(der_ref.to_owned())
    }
}

impl Der {
    /// Creates a new instance from `id` and `contents` .
    pub fn new(id: &IdRef, contents: &[u8]) -> Self {
        let len = Length::Definite(contents.len());
        let len = length::to_bytes(&len);

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
}

impl AsRef<[u8]> for Der {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

impl AsRef<DerRef> for Der {
    fn as_ref(&self) -> &DerRef {
        self.deref()
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
        unsafe { DerRef::from_bytes_unchecked(self.buffer.as_ref()) }
    }
}

pub fn disassemble_der(der: Der) -> Buffer {
    der.buffer
}

/// `DerBuilder` is a struct to build `Der` effectively.
///
/// # Examples
///
/// Empty contents.
///
/// ```
/// use bsn1::{Der, DerBuilder, IdRef, Length};
///
/// let id = IdRef::octet_string();
///
/// let expected = Der::new(IdRef::octet_string(), &[]);
///
/// // Because the contents is empty, do not need to call method 'extend_contents()'.
/// let mut builder = DerBuilder::new(id, Length::Definite(0));
/// let der = builder.finish();
///
/// assert_eq!(expected, der);
/// ```
///
/// Not empty contents
///
/// ```
/// use bsn1::{Der, DerBuilder, IdRef, Length};
///
/// let id = IdRef::octet_string();
///
/// let contents = &[0, 1, 2, 3, 4];
/// let expected = Der::new(IdRef::octet_string(), contents);
///
/// // Append 'contents' at once.
/// {
///     let length = Length::Definite(contents.len());
///     let mut builder = DerBuilder::new(id, length);
///     builder.extend_contents(contents);
///     let der = builder.finish();
///
///     assert_eq!(expected, der);
/// }
///
/// // Split contents into 2 pieces and append them one by one.
/// {
///     let length = Length::Definite(contents.len());
///     let mut builder = DerBuilder::new(id, length);
///     builder.extend_contents(&contents[..2]);
///     builder.extend_contents(&contents[2..]);
///     let der = builder.finish();
///
///     assert_eq!(expected, der);
/// }
/// ```
pub struct DerBuilder {
    buffer: Buffer,
    cursor: usize,
}

impl DerBuilder {
    /// Creates a new instance to build `Der` with `id` and contents whose length equals to
    /// `contents_len` .
    ///
    /// `contents_len` must be `Length::Definite` because 'DER' does not allow indefinite length.
    ///
    /// # Panics
    ///
    /// Panics if `contents_len` equals `Length::Indefinite` .
    pub fn new(id: &IdRef, contents_len: Length) -> Self {
        let length = length::to_bytes(&contents_len);
        let contents_len = match contents_len {
            Length::Definite(len) => len,
            Length::Indefinite => panic!("Indefinite length is specified to DerBuilder."),
        };

        let total_len = id.as_ref().len() + length.as_ref().len() + contents_len;
        let mut buffer = Buffer::with_capacity(total_len);
        unsafe { buffer.set_len(total_len) };

        let mut ret = Self { buffer, cursor: 0 };
        ret.extend_contents(id);
        ret.extend_contents(length);

        ret
    }

    /// Appends `bytes` to the end of the DER contents to be build.
    ///
    /// # Panics
    ///
    /// Panics if the accumerated length of the 'contents' exceeds `contents_len` that passed to
    /// the constructor function [`new`] as the argument.
    ///
    /// [`new`]: #method.new
    pub fn extend_contents<B>(&mut self, bytes: B)
    where
        B: AsRef<[u8]>,
    {
        let bytes = bytes.as_ref();
        assert!(self.cursor + bytes.len() <= self.buffer.len());

        unsafe {
            let ptr = self.buffer.as_mut_ptr().add(self.cursor);
            ptr.copy_from_nonoverlapping(bytes.as_ptr(), bytes.len());
            self.cursor += bytes.len();
        }
    }

    /// Consumes `self` , building a new `Der` .
    ///
    /// # Panics
    ///
    /// Panics if the accumerated length of the 'contents' differs from `contents_len` that passed
    /// to the constructor function [`new`] as the argument.
    ///
    /// [`new`]: #method.new
    pub fn finish(self) -> Der {
        assert_eq!(self.cursor, self.buffer.len());

        Der {
            buffer: self.buffer,
        }
    }
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
                assert_eq!(der_ref, der.as_ref());
            }
        }
    }
}
