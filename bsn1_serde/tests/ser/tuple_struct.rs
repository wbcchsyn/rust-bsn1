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

use bsn1::{ClassTag, Contents, DerRef, IdRef, PCTag};
use bsn1_serde::ser::Serialize as _;
use bsn1_serde::to_der;

#[derive(bsn1_serde::Serialize)]
struct A();

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde()]
struct B(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Set)]
struct C(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = UNIVERSAL)]
struct D(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = UNIVERSAL, id = Set)]
struct E(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_pc = CONSTRUCTED)]
struct F(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_pc = CONSTRUCTED, id = Set)]
struct G(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_pc = CONSTRUCTED, tag_class = UNIVERSAL)]
struct H(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_pc = CONSTRUCTED, tag_class = UNIVERSAL, id = Set)]
struct I(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0)]
struct J(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 1, id = Set)]
struct K(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0x1e, tag_class = UNIVERSAL)]
struct L(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0x1f, tag_class = UNIVERSAL, id = Set)]
struct M(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0x7f, tag_pc = CONSTRUCTED)]
struct N(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0x80, tag_pc = CONSTRUCTED, id = Set)]
struct O(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0x3fff, tag_pc = CONSTRUCTED, tag_class = UNIVERSAL)]
struct P(i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0x4000, tag_pc = CONSTRUCTED, tag_class = UNIVERSAL, id = Set)]
struct Q(i32, String);

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
    test_m();
    test_n();
    test_o();
    test_p();
    test_q();
}

fn test_a() {
    let val = A();
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id(), IdRef::sequence());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    assert_eq!(der.contents().len(), 0);
}

fn test_b() {
    let val = B(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_c() {
    let val = C(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_d() {
    let val = D(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_e() {
    let val = E(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_f() {
    let val = F(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_g() {
    let val = G(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_h() {
    let val = H(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_i() {
    let val = I(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_j() {
    let val = J(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_k() {
    let val = K(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), 1_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_l() {
    let val = L(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0x1e_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_m() {
    let val = M(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), 0x1f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_n() {
    let val = N(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x7f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_o() {
    let val = O(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x80_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_p() {
    let val = P(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x3fff_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_q() {
    let val = Q(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x4000_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(
        der.contents().len(),
        val.der_contents_len().unwrap().unwrap()
    );
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}
