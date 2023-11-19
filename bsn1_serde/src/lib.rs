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

#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

pub mod de;
pub mod ser;

use bsn1::{Ber, BerRef, Buffer, Der, Error, Length};
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
    unsafe { de::Deserialize::from_ber(ber.id(), ber.length(), ber.contents()) }
}
