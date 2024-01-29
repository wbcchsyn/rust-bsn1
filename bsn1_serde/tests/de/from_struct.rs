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

use bsn1_serde::{from_ber, from_der, to_ber, to_der};

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(into = "String", from = "String")]
struct A {
    inner: String,
}

impl Into<String> for A {
    fn into(self) -> String {
        self.inner
    }
}

impl From<String> for A {
    fn from(s: String) -> Self {
        Self { inner: s }
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(into = "String", from = "String")]
struct B {
    inner: String,
    _dummy: i8,
}

impl Into<String> for B {
    fn into(self) -> String {
        self.inner
    }
}

impl From<String> for B {
    fn from(s: String) -> Self {
        Self {
            inner: s,
            _dummy: 5,
        }
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(into = "String", from = "String")]
struct C(String);

impl Into<String> for C {
    fn into(self) -> String {
        self.0
    }
}

impl From<String> for C {
    fn from(s: String) -> Self {
        Self(s)
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(into = "String", from = "String")]
struct D(i8, String);

impl Into<String> for D {
    fn into(self) -> String {
        self.1
    }
}

impl From<String> for D {
    fn from(s: String) -> Self {
        Self(-2, s)
    }
}

fn main() {
    test_a();
    test_b();
    test_c();
    test_d();
}

fn test_a() {
    let val = A::from("abc".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_b() {
    let val = B::from("abc".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_c() {
    let val = C::from("abc".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_d() {
    let val = D::from("abc".to_string());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}
