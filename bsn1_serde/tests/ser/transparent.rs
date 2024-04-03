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
    #[bsn1_serde(skip)]
    _y: u8,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct D(
    #[bsn1_serde(into = "OctetString")] Vec<u8>,
    #[bsn1_serde(skip)] Option<String>,
);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct E {
    #[bsn1_serde(skip_serializing)]
    _x: i32,
    #[bsn1_serde(to = "OctetString::new")]
    y: String,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(transparent)]
struct F(
    #[bsn1_serde(skip_serializing)] String,
    #[bsn1_serde(to = "OctetString::new")] Vec<u8>,
);

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

    assert_eq!(der.id().len(), val.id_len().unwrap().unwrap());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
}

fn test_b() {
    let inner = String::from("abc");
    let val = B(inner.clone());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner).unwrap());

    assert_eq!(der.id().len(), val.id_len().unwrap().unwrap());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
}

fn test_c() {
    let x = String::from("abc");
    let y = 0x12;
    let val = C {
        x: x.clone(),
        _y: y,
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::from(x)).unwrap());

    assert!(val.id_len().unwrap().is_none());

    assert!(val.der_contents_len().unwrap().is_none());
}

fn test_d() {
    let inner = (vec![0x01, 0x02, 0x03], Some(String::from("abc")));
    let val = D(inner.0.clone(), inner.1.clone());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::from(inner.0)).unwrap());

    assert!(val.id_len().unwrap().is_none());

    assert!(val.der_contents_len().unwrap().is_none());
}

fn test_e() {
    let x = -0x1234;
    let y = String::from("abc");
    let val = E {
        _x: x,
        y: y.clone(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::new(&y)).unwrap());

    assert!(val.id_len().unwrap().is_none());

    assert!(val.der_contents_len().unwrap().is_none());
}

fn test_f() {
    let inner = (String::from(""), vec![0x01, 0x02, 0x03]);
    let val = F(inner.0.clone(), inner.1.clone());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&OctetString::new(&inner.1)).unwrap());

    assert!(val.id_len().unwrap().is_none());

    assert!(val.der_contents_len().unwrap().is_none());
}
