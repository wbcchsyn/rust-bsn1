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

use std::borrow::Cow;

/// `OctetString` is a wrapper of `std::borrow::Cow<[u8]>` and implements trait
/// [`crate::ser::Serialize`] and [`crate::de::Deserialize`].
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
