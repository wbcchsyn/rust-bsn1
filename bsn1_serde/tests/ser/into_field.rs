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
use bsn1_serde::to_der;

#[derive(Clone)]
struct Wrapper(i32);

impl Into<i32> for Wrapper {
    fn into(self) -> i32 {
        self.0
    }
}

#[derive(bsn1_serde::Serialize, Clone)]
struct A {
    #[bsn1_serde(into = "i32")]
    inner: Wrapper,
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(id = Set)]
struct B {
    #[bsn1_serde(into = "i32")]
    inner: Wrapper,
    dummy: i8,
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(id = Boolean)]
struct C(#[bsn1_serde(into = "i32")] Wrapper);

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(id = Null)]
struct D(i8, #[bsn1_serde(into = "i32")] Wrapper);

#[derive(bsn1_serde::Serialize, Clone)]
enum X {
    A {
        #[bsn1_serde(into = "i32")]
        inner: Wrapper,
    },
    #[bsn1_serde(id = Set)]
    B {
        #[bsn1_serde(into = "i32")]
        inner: Wrapper,
        dummy: i8,
    },
    #[bsn1_serde(id = Boolean)]
    C(#[bsn1_serde(into = "i32")] Wrapper),
    #[bsn1_serde(id = Null)]
    D(i8, #[bsn1_serde(into = "i32")] Wrapper),
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
        inner: Wrapper(123),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));

        assert_eq!(contents.len(), 0);
    }
}

fn test_b() {
    let val = B {
        inner: Wrapper(123),
        dummy: -4,
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));
        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));

        assert_eq!(contents.len(), 0);
    }
}

fn test_c() {
    let val = C(Wrapper(123));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::boolean());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));

        assert_eq!(contents.len(), 0);
    }
}

fn test_d() {
    let val = D(-4, Wrapper(123));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::null());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));
        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));

        assert_eq!(contents.len(), 0);
    }
}

fn test_xa() {
    let val = X::A {
        inner: Wrapper(123),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));

        assert_eq!(contents.len(), 0);
    }
}

fn test_xb() {
    let val = X::B {
        inner: Wrapper(123),
        dummy: -4,
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));
        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));

        assert_eq!(contents.len(), 0);
    }
}

fn test_xc() {
    let val = X::C(Wrapper(123));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::boolean());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));

        assert_eq!(contents.len(), 0);
    }
}

fn test_xd() {
    let val = X::D(-4, Wrapper(123));
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::null());
    assert_eq!(der.id().len(), val.id_len().unwrap());

    let contents = der.contents();
    {
        let mut contents: &[u8] = contents.as_ref();

        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(-4));
        assert_eq!(DerRef::parse(&mut contents).unwrap(), &Der::from(123));

        assert_eq!(contents.len(), 0);
    }
}
