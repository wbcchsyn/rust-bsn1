// Copyright 2023 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of bsn1_serde
//
//  bsn1_serde is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  bsn1_serde is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with bsn1_serde.  If not, see <http://www.gnu.org/licenses/>.
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

use crate::{de::Deserialize, ser::Serialize};
use bsn1::{ContentsRef, Error, IdRef, Length};
use std::borrow::Cow;
use std::io::Write;

/// `OctetString` is a wrapper of `std::borrow::Cow<[u8]>` and implements trait
/// [`Serialize`] and [`Deserialize`].
///
/// The identifier of `OctetString` is either `UNIVERSAL PRIMITIVE OctetString`
/// or `UNIVERSAL CONSTRUCTED OctetString` while that of `Vec<u8>` is `SEQUENCE OF INTEGER`.
///
/// Note that ASN.1 BER allows both `UNIVERSAL PRIMITIVE OctetString` and
/// `UNIVERSAL CONSTRUCTED OctetString` while ASN.1 DER allows only
/// `UNIVERSAL PRIMITIVE OctetString`.
///
/// `OctetString` is always serialized into `UNIVERSAL PRIMITIVE OctetString`, deserialized
/// as a DER from `UNIVERSAL PRIMITIVE OctetString`, and deserialized as a BER from
/// `UNIVERSAL PRIMITIVE OctetString` or `UNIVERSAL CONSTRUCTED OctetString`.
pub struct OctetString<'a> {
    octets: Cow<'a, [u8]>,
}

impl<'a> OctetString<'a> {
    /// Creates a new instance of `OctetString` from `val`.
    pub fn new<T>(val: &'a T) -> Self
    where
        T: ?Sized + AsRef<[u8]>,
    {
        Self {
            octets: Cow::Borrowed(val.as_ref()),
        }
    }

    /// Consumes `self` and returns the inner slice.
    pub fn into_vec(self) -> Vec<u8> {
        self.octets.into_owned()
    }
}

impl AsRef<[u8]> for OctetString<'_> {
    fn as_ref(&self) -> &[u8] {
        self.octets.as_ref()
    }
}

impl Serialize for OctetString<'_> {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        const ID: [u8; 1] = [0x04];
        buffer.write_all(&ID).map_err(Into::into)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer.write_all(&self.octets.as_ref()).map_err(Into::into)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        Ok(self.octets.len())
    }
}

impl Deserialize for OctetString<'static> {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::octet_string() && id != IdRef::octet_string_constructed() {
            return Err(Error::UnmatchedId);
        }
        if length.is_indefinite() {
            return Err(Error::IndefiniteLength);
        }

        Ok(Self {
            octets: Cow::Owned(contents.as_ref().to_vec()),
        })
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::octet_string() {
            return Err(Error::UnmatchedId);
        }

        Ok(Self {
            octets: Cow::Owned(contents.as_ref().to_vec()),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{from_ber, from_der, to_ber, to_der};

    #[test]
    fn serialize_octet_string() {
        const OCTETS: [u8; 3] = [0x01, 0x02, 0x03];
        let val = OctetString {
            octets: Cow::Borrowed(&OCTETS),
        };

        let der = to_der(&val).unwrap();
        assert_eq!(der.id(), IdRef::octet_string());
        assert_eq!(der.id().len(), val.id_len().unwrap());
        assert_eq!(der.contents().as_ref(), &OCTETS);
        assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    }

    #[test]
    fn deserialize_octet_string() {
        const OCTESTS: [u8; 3] = [0x01, 0x02, 0x03];
        let val = OctetString {
            octets: Cow::Borrowed(&OCTESTS),
        };

        let ber = to_ber(&val).unwrap();
        let deserialized: OctetString = from_ber(&ber).unwrap();
        assert_eq!(val.octets, deserialized.octets);

        let der = to_der(&val).unwrap();
        let deserialized: OctetString = from_der(&der).unwrap();
        assert_eq!(val.octets, deserialized.octets);
    }
}