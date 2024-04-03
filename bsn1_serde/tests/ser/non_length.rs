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

use bsn1::{DerRef, Error, IdRef};
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

    fn id_len(&self) -> Result<Option<usize>, Error> {
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

#[derive(Clone, Copy)]
struct NoneIdLen(i64);

impl ser::Serialize for NoneIdLen {
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        self.0.write_id(buffer)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        self.0.write_der_contents(buffer)
    }

    fn id_len(&self) -> Result<Option<usize>, Error> {
        Ok(None)
    }

    fn der_contents_len(&self) -> Result<Option<usize>, Error> {
        self.0.der_contents_len()
    }
}

impl From<i64> for NoneIdLen {
    fn from(val: i64) -> Self {
        NoneIdLen(val)
    }
}

impl Into<String> for NoneIdLen {
    fn into(self) -> String {
        self.0.to_string()
    }
}

impl NoneIdLen {
    pub fn to_string(&self) -> String {
        self.0.to_string()
    }
}

#[derive(Clone, Copy)]
struct NoneBothLen(i64);

impl ser::Serialize for NoneBothLen {
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        self.0.write_id(buffer)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        self.0.write_der_contents(buffer)
    }

    fn id_len(&self) -> Result<Option<usize>, Error> {
        Ok(None)
    }

    fn der_contents_len(&self) -> Result<Option<usize>, Error> {
        Ok(None)
    }
}

impl From<i64> for NoneBothLen {
    fn from(val: i64) -> Self {
        NoneBothLen(val)
    }
}

impl Into<String> for NoneBothLen {
    fn into(self) -> String {
        self.0.to_string()
    }
}

impl NoneBothLen {
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
#[bsn1_serde(transparent)]
struct E {
    x: NoneIdLen,
}

#[derive(Serialize)]
struct F(NoneIdLen);

#[derive(Serialize)]
#[bsn1_serde(id = Set)]
struct G {
    #[bsn1_serde(into = "String")]
    x: NoneIdLen,
}

#[derive(Serialize)]
#[bsn1_serde(transparent)]
struct H(#[bsn1_serde(to = "NoneIdLen::to_string")] NoneIdLen);

#[derive(Serialize)]
#[bsn1_serde(transparent)]
struct I {
    x: NoneBothLen,
}

#[derive(Serialize)]
#[bsn1_serde(transparent)]
struct J(NoneBothLen);

#[derive(Serialize)]
#[bsn1_serde(id = Set)]
struct K {
    #[bsn1_serde(into = "String")]
    x: NoneBothLen,
}

#[derive(Serialize)]
#[bsn1_serde(id = Set)]
struct Y {
    #[bsn1_serde(into = "String")]
    x: NoneDerContentsLen,
    #[bsn1_serde(to = "NoneIdLen::to_string")]
    y: NoneIdLen,
    z: NoneBothLen,
}

#[derive(Serialize)]
struct Z(
    #[bsn1_serde(into = "String")] NoneBothLen,
    NoneDerContentsLen,
    NoneIdLen,
);

#[derive(Serialize)]
#[bsn1_serde(id = Set)]
struct L(#[bsn1_serde(to = "NoneBothLen::to_string")] NoneBothLen);

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
    #[bsn1_serde(id = Set)]
    E {
        x: NoneIdLen,
    },
    #[bsn1_serde(id = Set)]
    F(NoneIdLen),
    G {
        #[bsn1_serde(into = "String")]
        x: NoneIdLen,
    },
    H(#[bsn1_serde(to = "NoneIdLen::to_string")] NoneIdLen),
    #[bsn1_serde(id = Set)]
    I {
        x: NoneBothLen,
    },
    J(NoneBothLen),
    K {
        #[bsn1_serde(into = "String")]
        x: NoneBothLen,
    },
    #[bsn1_serde(id = Set)]
    L(#[bsn1_serde(to = "NoneBothLen::to_string")] NoneBothLen),
    Y {
        #[bsn1_serde(into = "String")]
        x: NoneIdLen,
        y: NoneBothLen,
        z: NoneDerContentsLen,
    },
    #[bsn1_serde(id = Set)]
    Z(
        NoneDerContentsLen,
        #[bsn1_serde(into = "String")] NoneIdLen,
        #[bsn1_serde(to = "NoneBothLen::to_string")] NoneBothLen,
    ),
}

fn main() {
    test_a();
    test_b();
    test_c();
    test_d();
    test_e();
    test_f();
    test_g();
    test_h();
    test_i();
    test_j();
    test_k();
    test_l();

    test_y();
    test_z();

    test_xa();
    test_xb();
    test_xc();
    test_xd();
    test_xe();
    test_xf();
    test_xg();
    test_xh();
    test_xi();
    test_xj();
    test_xk();
    test_xl();

    test_xy();
    test_xz();
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

fn test_e() {
    let inner = 53;
    let val = E { x: inner.into() };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner).unwrap());
}

fn test_f() {
    let inner = -34;
    let val = F(inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_g() {
    let inner = 0;
    let val = G { x: inner.into() };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.to_string()).unwrap().as_ref() as &[u8]
    );
}

fn test_h() {
    let inner = 1;
    let val = H(inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner.to_string()).unwrap());
}

fn test_i() {
    let inner = 53;
    let val = I { x: inner.into() };
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner).unwrap());
}

fn test_j() {
    let inner = -34;
    let val = J(inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der, to_der(&inner).unwrap());
}

fn test_k() {
    let inner = 0;
    let val = K { x: inner.into() };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.to_string()).unwrap().as_ref() as &[u8]
    );
}

fn test_l() {
    let inner = 1;
    let val = L(inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.to_string()).unwrap().as_ref() as &[u8]
    );
}

fn test_y() {
    let inner = i64::MIN;
    let val = Y {
        x: inner.into(),
        y: inner.into(),
        z: inner.into(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());

    let mut contents: &[u8] = der.contents().as_ref();
    assert_eq!(
        to_der(&inner.to_string()).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner.to_string()).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert!(contents.is_empty());
}

fn test_z() {
    let inner = i64::MAX;
    let val = Z(inner.into(), inner.into(), inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());

    let mut contents: &[u8] = der.contents().as_ref();
    assert_eq!(
        to_der(&inner.to_string()).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert!(contents.is_empty());
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

fn test_xe() {
    let inner: NoneIdLen = 53.into();
    let val = NoneLenEnum::E { x: inner };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_xf() {
    let inner: NoneIdLen = (-34).into();
    let val = NoneLenEnum::F(inner);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_xg() {
    let inner: NoneIdLen = 0.into();
    let val = NoneLenEnum::G { x: inner };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.to_string()).unwrap().as_ref() as &[u8]
    );
}

fn test_xh() {
    let inner: NoneIdLen = 1.into();
    let val = NoneLenEnum::H(inner);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.into() as &String).unwrap().as_ref() as &[u8]
    );
}

fn test_xi() {
    let inner: NoneBothLen = 53.into();
    let val = NoneLenEnum::I { x: inner };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_xj() {
    let inner: NoneBothLen = (-34).into();
    let val = NoneLenEnum::J(inner);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner).unwrap().as_ref() as &[u8]
    );
}

fn test_xk() {
    let inner: NoneBothLen = 0.into();
    let val = NoneLenEnum::K { x: inner };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.to_string()).unwrap().as_ref() as &[u8]
    );
}

fn test_xl() {
    let inner: NoneBothLen = 1.into();
    let val = NoneLenEnum::L(inner);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());
    assert_eq!(
        der.contents().as_ref(),
        to_der(&inner.into() as &String).unwrap().as_ref() as &[u8]
    );
}

fn test_xy() {
    let inner = i64::MAX;
    let val = NoneLenEnum::Y {
        x: inner.into(),
        y: inner.into(),
        z: inner.into(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::sequence());

    let mut contents: &[u8] = der.contents().as_ref();
    assert_eq!(
        to_der(&inner.to_string()).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert!(contents.is_empty());
}

fn test_xz() {
    let inner = i64::MIN;
    let val = NoneLenEnum::Z(inner.into(), inner.into(), inner.into());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id(), IdRef::set());

    let mut contents: &[u8] = der.contents().as_ref();
    assert_eq!(
        to_der(&inner).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner.to_string()).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert_eq!(
        to_der(&inner.to_string()).unwrap(),
        DerRef::parse(&mut contents).unwrap()
    );
    assert!(contents.is_empty());
}
