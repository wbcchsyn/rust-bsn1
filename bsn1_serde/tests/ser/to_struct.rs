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

use bsn1::Der;
use bsn1_serde::ser::Serialize as _;
use bsn1_serde::{to_der, OctetString};

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(to = "OctetString::new")]
struct A {
    inner: String,
}

impl AsRef<[u8]> for A {
    fn as_ref(&self) -> &[u8] {
        self.inner.as_ref()
    }
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(to = "OctetString::new")]
struct B {
    _dummy: i8,
    inner: String,
}
impl AsRef<[u8]> for B {
    fn as_ref(&self) -> &[u8] {
        self.inner.as_ref()
    }
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(to = "OctetString::new")]
struct C(String);

impl AsRef<[u8]> for C {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(to = "OctetString::new")]
struct D(String, i8);

impl AsRef<[u8]> for D {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
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
    assert_eq!(der, Der::from(inner.as_bytes()));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_b() {
    let inner = "inner".to_string();
    let val = B {
        _dummy: 10,
        inner: inner.clone(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(der, Der::from(inner.as_bytes()));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_c() {
    let inner = "inner".to_string();
    let val = C(inner.clone());

    let der = to_der(&val).unwrap();
    assert_eq!(der, Der::from(inner.as_bytes()));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_d() {
    let inner = "inner".to_string();
    let val = D(inner.clone(), 10);

    let der = to_der(&val).unwrap();
    assert_eq!(der, Der::from(inner.as_bytes()));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}
