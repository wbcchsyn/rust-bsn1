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
use bsn1_serde::ser::Serialize as _;
use bsn1_serde::{to_der, OctetString};

struct Wrapper(Vec<u8>);

impl AsRef<[u8]> for Wrapper {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

#[derive(bsn1_serde::Serialize)]
struct A {
    #[bsn1_serde(to = "OctetString::new")]
    inner: Wrapper,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Set)]
struct B {
    #[bsn1_serde(to = "OctetString::new")]
    inner: Wrapper,
    dummy: i8,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Boolean)]
struct C(#[bsn1_serde(to = "OctetString::new")] Wrapper);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Null)]
struct D(i8, #[bsn1_serde(to = "OctetString::new")] Wrapper);

#[derive(bsn1_serde::Serialize)]
enum X {
    A {
        #[bsn1_serde(to = "OctetString::new")]
        inner: Wrapper,
    },
    #[bsn1_serde(id = Set)]
    B {
        #[bsn1_serde(to = "OctetString::new")]
        inner: Wrapper,
        dummy: i8,
    },
    #[bsn1_serde(id = Boolean)]
    C(#[bsn1_serde(to = "OctetString::new")] Wrapper),
    #[bsn1_serde(id = Null)]
    D(i8, #[bsn1_serde(to = "OctetString::new")] Wrapper),
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
    let inner = vec![];
    let val = A {
        inner: Wrapper(inner.clone()),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );

        assert_eq!(contents.len(), 0);
    }
}

fn test_b() {
    let inner = vec![1, 2, 3];
    let val = B {
        inner: Wrapper(inner.clone()),
        dummy: -4,
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );
        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));

        assert_eq!(contents.len(), 0);
    }
}

fn test_c() {
    let inner = vec![1, 2, 3, 4, 5];
    let val = C(Wrapper(inner.clone()));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::boolean());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );

        assert_eq!(contents.len(), 0);
    }
}

fn test_d() {
    let inner = vec![1, 2, 3, 4, 5, 6, 7];
    let val = D(-4, Wrapper(inner.clone()));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::null());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));
        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );

        assert_eq!(contents.len(), 0);
    }
}

fn test_xa() {
    let inner = vec![1, 2, 3, 4, 5, 6, 7, 8];
    let val = X::A {
        inner: Wrapper(inner.clone()),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );

        assert_eq!(contents.len(), 0);
    }
}

fn test_xb() {
    let inner = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    let val = X::B {
        inner: Wrapper(inner.clone()),
        dummy: -4,
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );
        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));

        assert_eq!(contents.len(), 0);
    }
}

fn test_xc() {
    let inner = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 0];
    let val = X::C(Wrapper(inner.clone()));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::boolean());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );

        assert_eq!(contents.len(), 0);
    }
}

fn test_xd() {
    let inner = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1];
    let val = X::D(-4, Wrapper(inner.clone()));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::null());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));
        assert_eq!(
            DerRef::parse(&mut contents).unwrap(),
            &Der::from(&inner[..])
        );

        assert_eq!(contents.len(), 0);
    }
}
