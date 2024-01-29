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

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
enum X {
    A(),
    //#[bsn1_serde()]
    //B (  i32,  String ),
    #[bsn1_serde(id = OctetString)]
    C(i32, String),
    #[bsn1_serde(tag_class = APPLICATION)]
    D(i32, String),
    #[bsn1_serde(tag_class = APPLICATION, id = OctetString)]
    E(i32, String),
    #[bsn1_serde(tag_pc = PRIMITIVE)]
    F(i32, String),
    //#[bsn1_serde(tag_pc = PRIMITIVE, id = OctetString)]
    //G (
    //     i32,
    //     String,
    //),
    //#[bsn1_serde(tag_pc = PRIMITIVE, tag_class = APPLICATION)]
    //H (
    //     i32,
    //     String,
    //),
    //#[bsn1_serde(tag_pc = PRIMITIVE, tag_class = APPLICATION, id = OctetString)]
    //I (
    //     i32,
    //     String,
    //),
    #[bsn1_serde(tag_num = 0)]
    J(i32, String),
    #[bsn1_serde(tag_num = 1, id = OctetString)]
    K(i32, String),
    #[bsn1_serde(tag_num = 0x1e, tag_class = APPLICATION)]
    L(i32, String),
    #[bsn1_serde(tag_num = 0x1f, tag_class = APPLICATION, id = OctetString)]
    M(i32, String),
    #[bsn1_serde(tag_num = 0x7f, tag_pc = PRIMITIVE)]
    N(i32, String),
    #[bsn1_serde(tag_num = 0x80, tag_pc = PRIMITIVE, id = OctetString)]
    O(i32, String),
    #[bsn1_serde(tag_num = 0x3fff, tag_pc = PRIMITIVE, tag_class = APPLICATION)]
    P(i32, String),
    #[bsn1_serde(tag_num = 0x4000, tag_pc = PRIMITIVE, tag_class = APPLICATION, id = OctetString)]
    Q(i32, String),
}

fn main() {
    test_xa();
    //test_xb();
    test_xc();
    test_xd();
    test_xe();
    test_xf();
    //test_xg();
    //test_xh();
    //test_xi();
    test_xj();
    test_xk();
    test_xl();
    test_xm();
    test_xn();
    test_xo();
    test_xp();
    test_xq();
}

fn test_xa() {
    let val = X::A();

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xc() {
    let val = X::C(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xd() {
    let val = X::D(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xe() {
    let val = X::E(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xf() {
    let val = X::F(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xj() {
    let val = X::J(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xk() {
    let val = X::K(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xl() {
    let val = X::L(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xm() {
    let val = X::M(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xn() {
    let val = X::N(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xo() {
    let val = X::O(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xp() {
    let val = X::P(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xq() {
    let val = X::Q(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}
