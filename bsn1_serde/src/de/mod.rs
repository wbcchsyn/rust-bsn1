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

//! Provides trait `Deserialize`.

use bsn1::{ContentsRef, Error, IdRef, Length};

/// A **data structure** that can be deserialized from ASN.1 DER format.
pub trait Deserialize: Sized {
    /// Deserializes `Self` from ASN.1 BER format.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `length` is invalid.
    ///
    /// ex)
    /// - `length` is indefinite where only definite length is allowed.
    /// - `length` is definite but the value does not match the length of `contents`.
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error>;

    /// Deserializes `Self` from ASN.1 DER format.
    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error>;
}

impl Deserialize for bool {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::boolean() {
            Err(Error::UnmatchedId)
        } else if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            contents.to_bool_ber()
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::boolean() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_bool_der()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{to_ber, to_der};

    #[test]
    fn boolean() {
        for b in [false, true] {
            let ber = to_ber(&b).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(b));

            let der = to_der(&b).unwrap();
            assert_eq!(crate::from_der(&der), Ok(b));
        }
    }
}
