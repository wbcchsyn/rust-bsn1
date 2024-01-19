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

#[derive(Clone, Debug, PartialEq)]
struct Wrapper(i32);

impl Into<i32> for Wrapper {
    fn into(self) -> i32 {
        self.0
    }
}

impl From<i32> for Wrapper {
    fn from(i: i32) -> Self {
        Self(i)
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct A {
    #[bsn1_serde(into = "i32", from = "i32")]
    inner: Wrapper,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct B {
    #[bsn1_serde(into = "i32", from = "i32")]
    inner: Wrapper,
    _dummy: i8,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct C(#[bsn1_serde(into = "i32", from = "i32")] Wrapper);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct D(i8, #[bsn1_serde(into = "i32", from = "i32")] Wrapper);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
enum X {
    #[bsn1_serde()]
    A {
        #[bsn1_serde(into = "i32", from = "i32")]
        inner: Wrapper,
    },
    #[bsn1_serde(id = Set)]
    B {
        #[bsn1_serde(into = "i32", from = "i32")]
        inner: Wrapper,
        _dummy: i8,
    },
    #[bsn1_serde(id = Set, tag_num = 0x0100)]
    C(#[bsn1_serde(into = "i32", from = "i32")] Wrapper),
    #[bsn1_serde(id = Set, tag_num = 0x0101)]
    D(i8, #[bsn1_serde(into = "i32", from = "i32")] Wrapper),
}

fn main() {
    test_a();
    test_b();
    test_c();
    test_d();
    test_xa();
    test_xb();
    test_xc();
    test_xd();
}

fn test_a() {
    let val = A {
        inner: Wrapper(123),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_b() {
    let val = B {
        inner: Wrapper(123),
        _dummy: 1,
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_c() {
    let val = C(Wrapper(123));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_d() {
    let val = D(1, Wrapper(123));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xa() {
    let val = X::A {
        inner: Wrapper(123),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xb() {
    let val = X::B {
        inner: Wrapper(123),
        _dummy: 1,
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xc() {
    let val = X::C(Wrapper(123));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xd() {
    let val = X::D(1, Wrapper(123));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}
