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

use crate::{identifier, length, Buffer, Der, DerRef, Error, IdRef, Length};
use core::convert::TryFrom;
use core::ops::Deref;
use std::borrow::Borrow;

/// `BerRef` is a wrapper of `[u8]` and represents 'BER' octets in 'ASN.1.'
///
/// This struct is 'Unsized', so usually user uses a reference to the instance.
#[derive(Debug, PartialEq, Eq)]
pub struct BerRef {
    bytes: [u8],
}

impl<'a> From<&'a DerRef> for &'a BerRef {
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
    /// Provides a reference from `bytes` without any sanitization.
    ///
    /// `bytes` must be 'ASN.1 BER' octets and must not include any extra octet.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` is not formatted as a 'BER'.
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        let ptr = bytes as *const [u8];
        let ptr = ptr as *const Self;
        &*ptr
    }

    /// Provides a reference from `bytes` that starts with an 'ASN.1 BER' octets.
    ///
    /// `bytes` may include some extra octet(s) at the end.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bytes` does not start with 'ASN.1 BER' octets.
    pub unsafe fn from_bytes_starts_with_unchecked(bytes: &[u8]) -> &Self {
        let id = identifier::shrink_to_fit_unchecked(bytes);
        let parsing = &bytes[id.len()..];

        let total_len = match length::try_from(parsing).unwrap() {
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
        let buffer = Buffer::from(self.as_ref());
        Ber { buffer }
    }
}

impl BerRef {
    /// Provides a reference to the `IdRef` of `self` .
    pub fn id(&self) -> &IdRef {
        unsafe {
            let bytes = identifier::shrink_to_fit_unchecked(&self.bytes);
            IdRef::from_bytes_unchecked(bytes)
        }
    }

    /// Returns the `Length` of `self` .
    pub fn length(&self) -> Length {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        length::try_from(bytes).unwrap().0
    }

    /// Provides a reference to the 'contents' of `self` .
    pub fn contents(&self) -> &[u8] {
        let id_len = self.id().as_ref().len();
        let bytes = &self.bytes[id_len..];
        length::try_from(bytes).unwrap().1
    }
}

/// `Ber` owns `BerRef` and represents 'BER' octets in 'ASN.1.'
#[derive(Debug, Clone, PartialEq, Eq)]
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

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let ber_ref = <&BerRef>::try_from(bytes)?;
        Ok(ber_ref.to_owned())
    }
}

impl Ber {
    /// Creates a new instance from `id` and `contents` with definite length.
    ///
    /// Note that 'BER' allows both 'definite length' and 'indefinite length', however, the
    /// return value is always 'definite length'.
    /// ('Indefinite length' is valid under some special condition, and the performance is usually
    /// worse than 'definite length.' Generally speaking, 'Indefinite length' is seldome used.)
    pub fn new(id: &IdRef, contents: &[u8]) -> Self {
        let der = Der::new(id, contents);
        Self::from(der)
    }
}

impl AsRef<[u8]> for Ber {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

impl AsRef<BerRef> for Ber {
    fn as_ref(&self) -> &BerRef {
        self.deref()
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
        unsafe { BerRef::from_bytes_unchecked(self.buffer.as_ref()) }
    }
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
            let ber = Ber::new(id, bytes);

            for &extra in extras {
                let mut bytes = Vec::from(ber.as_ref() as &[u8]);
                bytes.extend(extra);

                let ber_ref = unsafe { BerRef::from_bytes_starts_with_unchecked(bytes.as_ref()) };
                assert_eq!(ber_ref, ber.as_ref());
            }
        }
    }

    #[test]
    fn from_bytes_starts_with_unchecked_infinite() {
        let eoc = {
            let id = IdRef::eoc();
            let contents: &[u8] = &[];
            Ber::new(id, contents)
        };

        let bers: Vec<Ber> = (0..10)
            .map(|i| {
                let id = IdRef::octet_string();
                let contents: &[u8] = &[i];
                Ber::new(id, contents)
            })
            .collect();

        for i in 0..10 {
            let id = IdRef::sequence();
            let mut bytes: Vec<u8> = Vec::from(id.as_ref() as &[u8]);

            bytes.extend(length::to_bytes(&Length::Indefinite).as_ref());

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
            let ber = Ber::new(id, bytes);
            let ber_ref = <&BerRef>::try_from(ber.as_ref() as &[u8]).unwrap();
            assert_eq!(ber_ref, ber.as_ref() as &BerRef);
        }
    }

    #[test]
    fn try_from_indefinite() {
        let eoc = {
            let id = IdRef::eoc();
            let contents: &[u8] = &[];
            Ber::new(id, contents)
        };

        let bers: Vec<Ber> = (0..10)
            .map(|i| {
                let id = IdRef::octet_string();
                let contents: &[u8] = &[i];
                Ber::new(id, contents)
            })
            .collect();

        for i in 0..10 {
            let id = IdRef::sequence();
            let mut bytes: Vec<u8> = Vec::from(id.as_ref() as &[u8]);

            bytes.extend(length::to_bytes(&Length::Indefinite).as_ref());

            for ber in bers[0..i].iter() {
                bytes.extend(ber.as_ref() as &[u8]);
            }
            bytes.extend(eoc.as_ref() as &[u8]);

            let ber = <&BerRef>::try_from(bytes.as_ref() as &[u8]).unwrap();
            assert_eq!(bytes.as_ref() as &[u8], ber.as_ref() as &[u8]);
        }
    }
}