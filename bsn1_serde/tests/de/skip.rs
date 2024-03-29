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

use bsn1_serde::{from_ber, from_der, to_ber, to_der};

const fn two() -> i32 {
    2
}

fn bar() -> String {
    "bar".to_string()
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde]
struct B {
    #[bsn1_serde(skip, skip_deserializing, default = "Default::default")]
    _x: i32,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set)]
struct C {
    #[bsn1_serde(skip, default = "two")]
    _x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = PRIVATE)]
struct D {
    x: i32,
    #[bsn1_serde(skip, skip_serializing, skip_deserializing)]
    _y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_class = PRIVATE)]
struct E {
    x: i32,
    #[bsn1_serde(skip, skip_serializing, default = "bar")]
    _y: String,
    z: bool,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_pc = PRIMITIVE)]
struct F(#[bsn1_serde(skip, default = "two")] i32);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_pc = PRIMITIVE)]
struct G(#[bsn1_serde(skip, skip_deserializing)] i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = PRIVATE, tag_pc = PRIMITIVE)]
struct H(
    i32,
    #[bsn1_serde(skip, skip_serializing, default = "bar")] String,
);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_class = PRIVATE, tag_pc = PRIMITIVE)]
struct I(
    i32,
    #[bsn1_serde(
        skip,
        skip_serializing,
        skip_deserializing,
        default = "Default::default"
    )]
    String,
    bool,
);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
enum X {
    #[bsn1_serde(tag_num = 0)]
    J {
        #[bsn1_serde(skip, default = "two")]
        _x: i32,
    },
    #[bsn1_serde(id = Set, tag_num = 1)]
    K {
        #[bsn1_serde(skip, skip_deserializing)]
        _x: i32,
        y: String,
    },
    #[bsn1_serde(tag_class = PRIVATE, tag_num = 0x1e)]
    L {
        x: i32,
        #[bsn1_serde(skip, skip_serializing, default = "bar")]
        _y: String,
    },
    #[bsn1_serde(id = Set, tag_class = PRIVATE, tag_num = 0x1f)]
    M {
        x: i32,
        #[bsn1_serde(
            skip,
            skip_serializing,
            skip_deserializing,
            default = "Default::default"
        )]
        _y: String,
        z: bool,
    },
    #[bsn1_serde(tag_pc = PRIMITIVE, tag_num = 0x7f)]
    N(#[bsn1_serde(skip, skip_deserializing)] i32),
    #[bsn1_serde(id = Set, tag_pc = PRIMITIVE, tag_num = 0x80)]
    O(#[bsn1_serde(skip, default = "two")] i32, String),
    #[bsn1_serde(tag_class = PRIVATE, tag_pc = PRIMITIVE, tag_num = 0x3fff)]
    P(
        i32,
        #[bsn1_serde(
            skip,
            skip_serializing,
            skip_deserializing,
            default = "Default::default"
        )]
        String,
    ),
    #[bsn1_serde(
    id = Set,
    tag_class = PRIVATE,
    tag_pc = PRIMITIVE,
    tag_num = 0x4000)]
    Q(
        i32,
        #[bsn1_serde(skip, skip_serializing, default = "bar")] String,
        bool,
    ),
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
    let val = B { _x: 0 };
    let expected = B { _x: 0 };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_c() {
    let val = C {
        _x: 1,
        y: "foo".to_string(),
    };
    let expected = C {
        _x: 2,
        y: "foo".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_d() {
    let val = D {
        x: 0,
        _y: "".to_string(),
    };
    let expected = D {
        x: 0,
        _y: "".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_e() {
    let val = E {
        x: 1,
        _y: "foo".to_string(),
        z: true,
    };
    let expected = E {
        x: 1,
        _y: "bar".to_string(),
        z: true,
    };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_f() {
    let val = F(1);
    let expected = F(2);

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_g() {
    let val = G(0, "".to_string());
    let expected = G(0, "".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_h() {
    let val = H(1, "foo".to_string());
    let expected = H(1, "bar".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_i() {
    let val = I(0, "".to_string(), false);
    let expected = I(0, "".to_string(), false);

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xj() {
    let val = X::J { _x: 0 };
    let expected = X::J { _x: 2 };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xk() {
    let val = X::K {
        _x: 1,
        y: "foo".to_string(),
    };
    let expected = X::K {
        _x: 0,
        y: "foo".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xl() {
    let val = X::L {
        x: 0,
        _y: "".to_string(),
    };
    let expected = X::L {
        x: 0,
        _y: "bar".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xm() {
    let val = X::M {
        x: 1,
        _y: "foo".to_string(),
        z: true,
    };
    let expected = X::M {
        x: 1,
        _y: "".to_string(),
        z: true,
    };

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xn() {
    let val = X::N(1);
    let expected = X::N(0);

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xo() {
    let val = X::O(0, "".to_string());
    let expected = X::O(2, "".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xp() {
    let val = X::P(1, "foo".to_string());
    let expected = X::P(1, "".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}

fn test_xq() {
    let val = X::Q(0, "".to_string(), false);
    let expected = X::Q(0, "bar".to_string(), false);

    let der = to_der(&val).unwrap();
    assert_eq!(expected, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(expected, from_ber(&ber).unwrap());
}
