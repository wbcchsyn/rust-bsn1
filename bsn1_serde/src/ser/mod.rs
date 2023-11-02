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

//! Provides trait `Serialize`.

use ::bsn1::Error;
use std::io::Write;

/// A **data structure** that can be serialized into ASN.1 format.
pub trait Serialize {
    /// Writes the `ID` of ASN.1 format into `buffer` .
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error>;

    /// Serializes `self` into contents of ASN.1 DER format and writes it into `buffer` .
    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error>;

    /// Returns the byte count of the identifier of ASN.1 format.
    fn id_len(&self) -> Result<usize, Error>;

    /// Returns the byte count of the contents of ASN.1 DER format.
    fn der_contents_len(&self) -> Result<usize, Error>;
}
