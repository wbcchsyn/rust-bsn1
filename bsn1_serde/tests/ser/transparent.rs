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
use bsn1_serde::{to_der, OctetString};

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct A {
    x: Vec<u8>,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct B(String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct C {
    #[bsn1_serde(into = "OctetString")]
    x: String,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct D(#[bsn1_serde(into = "OctetString")] Vec<u8>);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct E {
    #[bsn1_serde(to = "OctetString::new")]
    x: String,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct F(#[bsn1_serde(to = "OctetString::new")] Vec<u8>);

fn main() {
    test_a();
    test_b();
    test_c();
    test_d();
    test_e();
    test_f();
}

fn test_a() {
    let inner = vec![0x01, 0x02, 0x03];
    let val = A { x: inner.clone() };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner).unwrap());

    assert_eq!(der.id().len(), val.id_len().unwrap());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_b() {
    let inner = String::from("abc");
    let val = B(inner.clone());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner).unwrap());

    assert_eq!(der.id().len(), val.id_len().unwrap());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_c() {
    let inner = String::from("abc");
    let val = C { x: inner.clone() };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::from(inner)).unwrap());

    assert_eq!(der.id().len(), val.id_len().unwrap());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_d() {
    let inner = vec![0x01, 0x02, 0x03];
    let val = D(inner.clone());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::from(inner)).unwrap());

    assert_eq!(der.id().len(), val.id_len().unwrap());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_e() {
    let inner = String::from("abc");
    let val = E { x: inner.clone() };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::new(&inner)).unwrap());

    assert_eq!(der.id().len(), val.id_len().unwrap());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_f() {
    let inner = vec![0x01, 0x02, 0x03];
    let val = F(inner.clone());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::new(&inner)).unwrap());

    assert_eq!(der.id().len(), val.id_len().unwrap());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}
