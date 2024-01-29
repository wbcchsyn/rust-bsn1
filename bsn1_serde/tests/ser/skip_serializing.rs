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

use bsn1::{ClassTag, Der, DerRef, IdRef, PCTag};
use bsn1_serde::ser::Serialize as _;
use bsn1_serde::to_der;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde]
struct B {
    #[bsn1_serde(skip_serializing)]
    _x: i32,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer)]
struct C {
    #[bsn1_serde(skip_serializing)]
    _x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = APPLICATION)]
struct D {
    x: i32,
    #[bsn1_serde(skip_serializing)]
    _y: String,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_class = APPLICATION)]
struct E {
    x: i32,
    #[bsn1_serde(skip_serializing)]
    _y: String,
    z: bool,
}

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_pc = CONSTRUCTED)]
struct F(#[bsn1_serde(skip_serializing)] i32);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_pc = CONSTRUCTED)]
struct G(#[bsn1_serde(skip_serializing)] i32, String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = APPLICATION, tag_pc = CONSTRUCTED)]
struct H(i32, #[bsn1_serde(skip_serializing)] String);

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_class = APPLICATION, tag_pc = CONSTRUCTED)]
struct I(i32, #[bsn1_serde(skip_serializing)] String, bool);

#[derive(bsn1_serde::Serialize)]
enum X {
    #[bsn1_serde(tag_num = 0)]
    J {
        #[bsn1_serde(skip_serializing)]
        _x: i32,
    },
    #[bsn1_serde(id = Integer, tag_num = 1)]
    K {
        #[bsn1_serde(skip_serializing)]
        _x: i32,
        y: String,
    },
    #[bsn1_serde(tag_class = APPLICATION, tag_num = 0x1e)]
    L {
        x: i32,
        #[bsn1_serde(skip_serializing)]
        _y: String,
    },
    #[bsn1_serde(id = Integer, tag_class = APPLICATION, tag_num = 0x1f)]
    M {
        x: i32,
        #[bsn1_serde(skip_serializing)]
        _y: String,
        z: bool,
    },
    #[bsn1_serde(tag_pc = CONSTRUCTED, tag_num = 0x7f)]
    N(#[bsn1_serde(skip_serializing)] i32),
    #[bsn1_serde(id = Integer, tag_pc = CONSTRUCTED, tag_num = 0x80)]
    O(#[bsn1_serde(skip_serializing)] i32, String),
    #[bsn1_serde(tag_class = APPLICATION, tag_pc = CONSTRUCTED, tag_num = 0x3fff)]
    P(i32, #[bsn1_serde(skip_serializing)] String),
    #[bsn1_serde(
    id = Integer,
    tag_class = APPLICATION,
    tag_pc = CONSTRUCTED,
    tag_num = 0x4000)]
    Q(i32, #[bsn1_serde(skip_serializing)] String, bool),
}

fn main() {
    test_b();
    test_c();
    test_d();
    test_e();
    test_f();
    test_g();
    test_h();
    test_i();
    test_xj();
    test_xk();
    test_xl();
    test_xm();
    test_xn();
    test_xo();
    test_xp();
    test_xq();
}

fn test_b() {
    let val = B { _x: 315 };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_c() {
    let val = C {
        _x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::integer().class());
    assert_eq!(der.id().pc(), IdRef::integer().pc());
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::integer().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_d() {
    let val = D {
        x: 315,
        _y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315_i32));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_e() {
    let val = E {
        x: 315,
        _y: "foo".to_string(),
        z: true,
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::integer().pc());
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::integer().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1, &Der::from(true));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_f() {
    let val = F(315);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_g() {
    let val = G(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::integer().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::integer().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_h() {
    let val = H(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_i() {
    let val = I(315, "foo".to_string(), false);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::integer().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1, &Der::from(false));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xj() {
    let val = X::J { _x: 315 };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xk() {
    let val = X::K {
        _x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::integer().class());
    assert_eq!(der.id().pc(), IdRef::integer().pc());
    assert_eq!(der.id().number().unwrap(), 1_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xl() {
    let val = X::L {
        x: 315,
        _y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0x1e_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315_i32));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xm() {
    let val = X::M {
        x: 315,
        _y: "foo".to_string(),
        z: true,
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::integer().pc());
    assert_eq!(der.id().number().unwrap(), 0x1f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1, &Der::from(true));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xn() {
    let val = X::N(315);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x7f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xo() {
    let val = X::O(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::integer().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x80_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xp() {
    let val = X::P(315, "foo".to_string());
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x3fff_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315_i32));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xq() {
    let val = X::Q(315, "foo".to_string(), false);
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x4000_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0, &Der::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1, &Der::from(false));

        assert_eq!(contents.is_empty(), true);
    }
}
