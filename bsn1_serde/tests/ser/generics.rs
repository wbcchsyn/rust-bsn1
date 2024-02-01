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

use bsn1::{Der, DerRef, IdRef};
use bsn1_serde::ser::Serialize;
use bsn1_serde::{to_der, OctetString};

#[derive(bsn1_serde::Serialize)]
struct A<'a, 'b: 'static, C, D: Clone + Copy + Serialize, const M: usize, const N: usize = 3>
where
    C: Serialize,
{
    #[bsn1_serde(to = "OctetString::new")]
    a: &'a [u8],
    #[bsn1_serde(to = "OctetString::new")]
    b: &'b [u8],
    c: C,
    d: D,
    #[bsn1_serde(to = "OctetString::new")]
    e: [u8; M],
    #[bsn1_serde(to = "OctetString::new")]
    f: [u8; N],
}

fn main() {
    test_a();
}

fn test_a() {
    let a = &[0x01, 0x02, 0x03];
    let b = &[];
    let c = true;
    let d = 53;
    let e = [0x04, 0x05, 0x06, 0x07];
    let f = [0x08, 0x09];

    let val = A { a, b, c, d, e, f };

    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());

    let contents = der.contents();
    let mut contents: &[u8] = contents.as_ref();

    {
        let der = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der.id(), IdRef::octet_string());
        assert_eq!(der.contents().as_ref() as &[u8], a);
    }

    {
        let der = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der.id(), IdRef::octet_string());
        assert_eq!(der.contents().as_ref() as &[u8], b);
    }

    {
        let der = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der, &Der::from(c));
    }

    {
        let der = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der, &Der::from(d));
    }

    {
        let der = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der.id(), IdRef::octet_string());
        assert_eq!(der.contents().as_ref() as &[u8], e);
    }

    {
        let der = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der.id(), IdRef::octet_string());
        assert_eq!(der.contents().as_ref() as &[u8], f);
    }
}
