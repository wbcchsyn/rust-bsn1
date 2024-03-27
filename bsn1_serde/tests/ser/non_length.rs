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

use bsn1::{Error, IdRef};
use bsn1_serde::{ser, to_der, Serialize};
use std::io::Write;

#[derive(Clone, Copy)]
struct NoneDerContentsLen(i64);

impl ser::Serialize for NoneDerContentsLen {
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        self.0.write_id(buffer)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        self.0.write_der_contents(buffer)
    }

    fn id_len(&self) -> Result<usize, Error> {
        self.0.id_len()
    }

    fn der_contents_len(&self) -> Result<Option<usize>, Error> {
        Ok(None)
    }
}

impl From<i64> for NoneDerContentsLen {
    fn from(val: i64) -> Self {
        NoneDerContentsLen(val)
    }
}

impl Into<String> for NoneDerContentsLen {
    fn into(self) -> String {
        self.0.to_string()
    }
}

impl NoneDerContentsLen {
    pub fn to_string(&self) -> String {
        self.0.to_string()
    }
}

#[derive(Serialize)]
struct A {
    x: NoneDerContentsLen,
}

#[derive(Serialize)]
#[bsn1_serde(transparent)]
struct B(NoneDerContentsLen);

#[derive(Serialize)]
#[bsn1_serde(transparent)]
struct C {
    #[bsn1_serde(to = "NoneDerContentsLen::to_string")]
    x: NoneDerContentsLen,
}

#[derive(Serialize)]
#[bsn1_serde(id = Set)]
struct D(#[bsn1_serde(into = "String")] NoneDerContentsLen);

#[derive(Serialize)]
enum NoneLenEnum {
    A {
        x: NoneDerContentsLen,
    },
    B(NoneDerContentsLen),
    #[bsn1_serde(id = Set)]
    C {
        #[bsn1_serde(to = "NoneDerContentsLen::to_string")]
        x: NoneDerContentsLen,
    },
    #[bsn1_serde(id = Set)]
    D(#[bsn1_serde(into = "String")] NoneDerContentsLen),
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
    let inner = 53;
    let val = A { x: inner.into() };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_b() {
    let inner = -34;
    let val = B(inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner).unwrap());
}

fn test_c() {
    let inner = 0;
    let val = C { x: inner.into() };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner.to_string()).unwrap());
}

fn test_d() {
    let inner = 1;
    let val = D(inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.to_string()).unwrap().as_ref() as &[u8]
    );
}

fn test_xa() {
    let inner: NoneDerContentsLen = 53.into();
    let val = NoneLenEnum::A { x: inner };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_xb() {
    let inner: NoneDerContentsLen = (-34).into();
    let val = NoneLenEnum::B(inner);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_xc() {
    let inner: NoneDerContentsLen = 0.into();
    let val = NoneLenEnum::C { x: inner };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.to_string()).unwrap().as_ref() as &[u8]
    );
}

fn test_xd() {
    let inner: NoneDerContentsLen = 1.into();
    let val = NoneLenEnum::D(inner);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.into() as &String).unwrap().as_ref() as &[u8]
    );
}
