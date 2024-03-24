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

use bsn1_serde::{from_ber, from_der, to_ber, to_der, OctetString};

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(transparent)]
struct A {
    x: Vec<u8>,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(transparent)]
struct B(String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(transparent)]
struct C {
    #[bsn1_serde(from = "OctetString<'static>", into = "OctetString")]
    x: Vec<u8>,
    #[bsn1_serde(skip)]
    y: u8,
}

#[derive(bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(transparent)]
struct D(
    #[bsn1_serde(from = "OctetString<'static>")] Vec<u8>,
    #[bsn1_serde(skip_deserializing)] String,
);

#[derive(bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(transparent)]
struct E {
    #[bsn1_serde(skip_deserializing)]
    x: String,
    #[bsn1_serde(try_from = "OctetString", to = "OctetString::new")]
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(transparent)]
struct F(
    #[bsn1_serde(skip)] u8,
    #[bsn1_serde(try_from = "OctetString", to = "OctetString::new")] String,
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
    let val = A {
        x: vec![0x01, 0x02, 0x03],
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_b() {
    let val = B("abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_c() {
    let val = C {
        x: vec![0x01, 0x02, 0x03],
        y: 0x04,
    };

    let der = to_der(&val).unwrap();
    let val2: C = from_der(&der).unwrap();
    assert_eq!(val2.x, val.x);
    assert_eq!(val2.y, Default::default());

    let ber = to_ber(&val).unwrap();
    let val3: C = from_ber(&ber).unwrap();
    assert_eq!(val3.x, val.x);
    assert_eq!(val3.y, Default::default());
}

fn test_d() {
    let inner0: Vec<u8> = vec![0x01, 0x02, 0x03];

    let der = to_der(&OctetString::new(&inner0)).unwrap();
    let val: D = from_der(&der).unwrap();
    assert_eq!(val.0, inner0);
    assert_eq!(val.1, String::default());

    let ber = to_ber(&OctetString::new(&inner0)).unwrap();
    let val: D = from_ber(&ber).unwrap();
    assert_eq!(val.0, inner0);
    assert_eq!(val.1, String::default());
}

fn test_e() {
    let y = "foo".to_string();

    let der = to_der(&OctetString::new(&y)).unwrap();
    let val: E = from_der(&der).unwrap();
    assert_eq!(val.x, String::default());
    assert_eq!(val.y, y);

    let ber = to_ber(&OctetString::new(&y)).unwrap();
    let val: E = from_ber(&ber).unwrap();
    assert_eq!(val.x, String::default());
    assert_eq!(val.y, y);
}

fn test_f() {
    let inner1 = "bar".to_string();
    let val = F(3, inner1.clone());

    let der = to_der(&val).unwrap();
    let val2: F = from_der(&der).unwrap();
    assert_eq!(val2.0, u8::default());
    assert_eq!(val2.1, inner1);

    let ber = to_ber(&val).unwrap();
    let val3: F = from_ber(&ber).unwrap();
    assert_eq!(val3.0, u8::default());
    assert_eq!(val3.1, inner1);
}
