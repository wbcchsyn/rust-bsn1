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
enum X {
    A { inner: String },
    B { inner: String, _dummy: i8 },
    C(String),
    D(i8, String),
}

impl TryFrom<OctetString<'_>> for X {
    type Error = std::string::FromUtf8Error;

    fn try_from(octet_string: OctetString) -> Result<Self, Self::Error> {
        let inner = String::from_utf8(octet_string.into_vec())?;

        match inner.chars().next().unwrap() {
            'a' => Ok(Self::A { inner }),
            'b' => Ok(Self::B { inner, _dummy: 2 }),
            'c' => Ok(Self::C(inner)),
            'd' => Ok(Self::D(3, inner)),
            _ => unreachable!(),
        }
    }
}

impl AsRef<[u8]> for X {
    fn as_ref(&self) -> &[u8] {
        match self {
            Self::A { inner } => inner.as_bytes(),
            Self::B { inner, .. } => inner.as_bytes(),
            Self::C(inner) => inner.as_bytes(),
            Self::D(_, inner) => inner.as_bytes(),
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
    let val = X::try_from(OctetString::new("aaa".as_bytes())).unwrap();

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_xb() {
    let val = X::try_from(OctetString::new("bbb".as_bytes())).unwrap();

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_xc() {
    let val = X::try_from(OctetString::new("ccc".as_bytes())).unwrap();

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}

fn test_xd() {
    let val = X::try_from(OctetString::new("ddd".as_bytes())).unwrap();

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());
}
