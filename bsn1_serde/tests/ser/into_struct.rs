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

use bsn1_serde::ser::Serialize as _;
use bsn1_serde::to_der;

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct A {
    inner: String,
}

impl Into<String> for A {
    fn into(self) -> String {
        self.inner
    }
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct B {
    _dummy: i8,
    inner: String,
}

impl Into<String> for B {
    fn into(self) -> String {
        self.inner
    }
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct C(String);

impl Into<String> for C {
    fn into(self) -> String {
        self.0
    }
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct D(String, i8);

impl Into<String> for D {
    fn into(self) -> String {
        self.0
    }
}

fn main() {
    test_a();
    test_b();
    test_c();
    test_d();
}

fn test_a() {
    let inner = "inner".to_string();
    let val = A {
        inner: inner.clone(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert!(val.id_len().unwrap().is_none());
    assert!(val.der_contents_len().unwrap().is_none());
}

fn test_b() {
    let inner = "inner".to_string();
    let val = B {
        _dummy: 10,
        inner: inner.clone(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert!(val.id_len().unwrap().is_none());
    assert!(val.der_contents_len().unwrap().is_none());
}

fn test_c() {
    let inner = "inner".to_string();
    let val = C(inner.clone());

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert!(val.id_len().unwrap().is_none());
    assert!(val.der_contents_len().unwrap().is_none());
}

fn test_d() {
    let inner = "inner".to_string();
    let val = D(inner.clone(), 10);

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert!(val.id_len().unwrap().is_none());
    assert!(val.der_contents_len().unwrap().is_none());
}
