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

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(to = "OctetString::new", try_from = "OctetString")]
struct A {
    inner: String,
}

impl TryFrom<OctetString<'_>> for A {
    type Error = std::string::FromUtf8Error;

    fn try_from(octet_string: OctetString) -> Result<Self, Self::Error> {
        Ok(Self {
            inner: String::from_utf8(octet_string.into_vec())?,
        })
    }
}

impl AsRef<[u8]> for A {
    fn as_ref(&self) -> &[u8] {
        self.inner.as_bytes()
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(to = "OctetString::new", try_from = "OctetString")]
struct B {
    inner: String,
    _dummy: i8,
}

impl TryFrom<OctetString<'_>> for B {
    type Error = std::string::FromUtf8Error;

    fn try_from(octet_string: OctetString) -> Result<Self, Self::Error> {
        Ok(Self {
            inner: String::from_utf8(octet_string.into_vec())?,
            _dummy: -2,
        })
    }
}

impl AsRef<[u8]> for B {
    fn as_ref(&self) -> &[u8] {
        self.inner.as_bytes()
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(to = "OctetString::new", try_from = "OctetString")]
struct C(String);

impl TryFrom<OctetString<'_>> for C {
    type Error = std::string::FromUtf8Error;

    fn try_from(octet_string: OctetString) -> Result<Self, Self::Error> {
        Ok(Self(String::from_utf8(octet_string.into_vec())?))
    }
}

impl AsRef<[u8]> for C {
    fn as_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Clone, Debug, PartialEq)]
#[bsn1_serde(to = "OctetString::new", try_from = "OctetString")]
struct D(i8, String);

impl TryFrom<OctetString<'_>> for D {
    type Error = std::string::FromUtf8Error;

    fn try_from(octet_string: OctetString) -> Result<Self, Self::Error> {
        Ok(Self(3, String::from_utf8(octet_string.into_vec())?))
    }
}

impl AsRef<[u8]> for D {
    fn as_ref(&self) -> &[u8] {
        self.1.as_bytes()
    }
}

fn main() {
    test_a();
    test_b();
    test_c();
    test_d();
}

fn test_a() {
    let val = A::try_from(OctetString::new("abc")).unwrap();
    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_b() {
    let val = B::try_from(OctetString::new("abc")).unwrap();

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_c() {
    let val = C::try_from(OctetString::new("abc")).unwrap();

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_d() {
    let val = D::try_from(OctetString::new("abc")).unwrap();

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}
