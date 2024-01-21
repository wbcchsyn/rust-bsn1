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

use bsn1_serde::ser::Serialize as _;
use bsn1_serde::to_der;

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "i32")]
enum X {
    A { inner: i32 },
    B { inner: i32, _dummy: i8 },
    C(i32),
    D(i8, i32),
}

impl Into<i32> for X {
    fn into(self) -> i32 {
        match self {
            X::A { inner } => inner,
            X::B { inner, .. } => inner,
            X::C(inner, ..) => inner,
            X::D(_, inner) => inner,
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
    let inner = 5;
    let val = X::A { inner };

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_xb() {
    let inner = 5;
    let val = X::B { _dummy: -2, inner };

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_xc() {
    let inner = 5;
    let val = X::C(inner);

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_xd() {
    let inner = 5;
    let val = X::D(-2, inner);

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}