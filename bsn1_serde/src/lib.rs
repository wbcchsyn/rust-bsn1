// Copyright 2023-2024 Shin Yoshida
//
// "GPL-3.0-only"
//
// This is part of BSN1_SERDE
//
// BSN1_SERDE is free software: you can redistribute it and/or modify it under the terms of the
// GNU General Public License as published by the Free Software Foundation, version 3.
//
// BSN1_SERDE is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
// even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with this program. If
// not, see <https://www.gnu.org/licenses/>.

#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

pub mod de;
#[doc(hidden)]
pub mod macro_alias;
mod octet_string;
pub mod ser;

use bsn1::{Ber, BerRef, Buffer, Der, DerRef, Error, Length};
pub use bsn1_serde_macros::{Deserialize, Serialize};
pub use octet_string::OctetString;
use std::io::Write as _;

/// Serializes `value` into ASN.1 DER format.
pub fn to_der<T>(value: &T) -> Result<Der, Error>
where
    T: ?Sized + ser::Serialize,
{
    let contents_len = value.der_contents_len()?;
    let length = Length::Definite(contents_len).to_bytes();
    let der_len = value.id_len()? + length.len() + contents_len;

    let mut buffer = Buffer::with_capacity(der_len);
    value.write_id(&mut buffer)?;
    buffer.write_all(&length).unwrap(); // Buffer::write_all() never fails.
    value.write_der_contents(&mut buffer)?;

    Ok(buffer.into())
}

/// Serializes `value` into ASN.1 BER format.
pub fn to_ber<T>(value: &T) -> Result<Ber, Error>
where
    T: ?Sized + ser::Serialize,
{
    // DER is always valid as BER.
    to_der(value).map(Ber::from)
}

/// Deserializes `T` from ASN.1 BER format.
pub fn from_ber<T>(ber: &BerRef) -> Result<T, Error>
where
    T: de::Deserialize,
{
    let (id, length, contents) = ber.disassemble();
    unsafe { de::Deserialize::from_ber(id, length, contents) }
}

/// Deserializes `T` from ASN.1 DER format.
pub fn from_der<T>(der: &DerRef) -> Result<T, Error>
where
    T: de::Deserialize,
{
    let (id, _, contents) = der.disassemble();
    de::Deserialize::from_der(id, contents)
}
