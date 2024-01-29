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

#[derive(Debug, PartialEq)]
struct Wrapper(Vec<u8>);

impl AsRef<[u8]> for Wrapper {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl From<OctetString<'_>> for Wrapper {
    fn from(octet_string: OctetString) -> Self {
        Self(octet_string.into_vec())
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct A {
    #[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")]
    inner: Wrapper,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct B {
    #[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")]
    inner: Wrapper,
    _dummy: i8,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean)]
struct C(#[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")] Wrapper);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Null)]
struct D(
    i8,
    #[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")] Wrapper,
);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
enum X {
    A {
        #[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")]
        inner: Wrapper,
    },
    #[bsn1_serde(id = Set)]
    B {
        #[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")]
        inner: Wrapper,
        _dummy: i8,
    },
    #[bsn1_serde(id = Boolean)]
    C(#[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")] Wrapper),
    #[bsn1_serde(id = Null)]
    D(
        i8,
        #[bsn1_serde(to = "OctetString::new", try_from = "OctetString<'_>")] Wrapper,
    ),
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
        inner: Wrapper::from(OctetString::new(&[] as &[u8])),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_b() {
    let val = B {
        inner: Wrapper::from(OctetString::new(&[0])),
        _dummy: 1,
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_c() {
    let val = C(Wrapper::from(OctetString::new(&[0, 1])));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_d() {
    let val = D(1, Wrapper::from(OctetString::new(&[0, 1, 2])));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xa() {
    let val = X::A {
        inner: Wrapper::from(OctetString::new(&[] as &[u8])),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xb() {
    let val = X::B {
        inner: Wrapper::from(OctetString::new(&[0])),
        _dummy: 1,
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xc() {
    let val = X::C(Wrapper::from(OctetString::new(&[0, 1])));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xd() {
    let val = X::D(1, Wrapper::from(OctetString::new(&[0, 1, 2])));

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}
