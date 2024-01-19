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

use bsn1_serde::{from_ber, from_der, to_ber, to_der};

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(into = "String", from = "String")]
enum X {
    A { inner: String },
    B { inner: String, _dummy: i8 },
    C(String),
    D(i8, String),
}

impl Into<String> for X {
    fn into(self) -> String {
        match self {
            Self::A { inner } => inner,
            Self::B { inner, .. } => inner,
            Self::C(inner) => inner,
            Self::D(_, inner) => inner,
        }
    }
}

impl From<String> for X {
    fn from(s: String) -> Self {
        if s.starts_with('a') {
            Self::A { inner: s }
        } else if s.starts_with('b') {
            Self::B {
                inner: s,
                _dummy: 7,
            }
        } else if s.starts_with('c') {
            Self::C(s)
        } else {
            Self::D(13, s)
        }
    }
}

fn main() {
    test_xa();
    test_xb();
    test_xc();
    test_xd();
}

fn test_xa() {
    let val = X::from("a_foo".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_xb() {
    let val = X::from("b_foo".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_xc() {
    let val = X::from("c_foo".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_xd() {
    let val = X::from("d_foo".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}
