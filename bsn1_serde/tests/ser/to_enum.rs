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
enum X {
    A { inner: [u8; 3] },
    B { inner: [u8; 3], _dummy: i8 },
    C([u8; 3]),
    D(i8, [u8; 3]),
}

impl AsRef<[u8]> for X {
    fn as_ref(&self) -> &[u8] {
        match self {
            X::A { inner } => inner,
            X::B { inner, .. } => inner,
            X::C(inner) => inner,
            X::D(_, inner) => inner,
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
    const INNER: [u8; 3] = [1, 2, 3];
    let val = X::A { inner: INNER };

    let der = to_der(&val).unwrap();
    assert_eq!(der, Der::from(&INNER as &[u8]));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_xb() {
    const INNER: [u8; 3] = [1, 2, 3];
    let val = X::B {
        _dummy: -2,
        inner: INNER,
    };

    let der = to_der(&val).unwrap();
    assert_eq!(der, Der::from(&INNER as &[u8]));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_xc() {
    const INNER: [u8; 3] = [1, 2, 3];
    let val = X::C(INNER);

    let der = to_der(&val).unwrap();
    assert_eq!(der, Der::from(&INNER as &[u8]));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_xd() {
    const INNER: [u8; 3] = [1, 2, 3];
    let val = X::D(-2, INNER);

    let der = to_der(&val).unwrap();
    assert_eq!(der, Der::from(&INNER as &[u8]));
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}
