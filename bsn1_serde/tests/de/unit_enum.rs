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
    //A,
    #[bsn1_serde()]
    B,
    #[bsn1_serde(id = Set)]
    C,
    #[bsn1_serde(tag_class = CONTEXT_SPECIFIC)]
    D,
    #[bsn1_serde(tag_class = CONTEXT_SPECIFIC, id = Set)]
    E,
    #[bsn1_serde(tag_pc = PRIMITIVE)]
    F,
    #[bsn1_serde(tag_pc = PRIMITIVE, id = Set)]
    G,
    #[bsn1_serde(tag_pc = PRIMITIVE, tag_class = CONTEXT_SPECIFIC)]
    H,
    #[bsn1_serde(tag_pc = PRIMITIVE, tag_class = CONTEXT_SPECIFIC, id = Set)]
    I,
    #[bsn1_serde(tag_num = 0)]
    J,
    #[bsn1_serde(tag_num = 1, id = Set)]
    K,
    #[bsn1_serde(tag_num = 0x1e, tag_class = CONTEXT_SPECIFIC)]
    L,
    #[bsn1_serde(tag_num = 0x1f, tag_class = CONTEXT_SPECIFIC, id = Set)]
    M,
    #[bsn1_serde(tag_num = 0x7f, tag_pc = PRIMITIVE)]
    N,
    #[bsn1_serde(tag_num = 0x80, tag_pc = PRIMITIVE, id = Set)]
    O,
    #[bsn1_serde(tag_num = 0x3fff, tag_pc = PRIMITIVE, tag_class = CONTEXT_SPECIFIC)]
    P,
    #[bsn1_serde(tag_num = 0x4000, tag_pc = PRIMITIVE, tag_class = CONTEXT_SPECIFIC, id = Set)]
    Q,
}

fn main() {
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
    test_xm();
    test_xn();
    test_xo();
    test_xp();
    test_xq();
}

fn test_xb() {
    let val = X::B;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xc() {
    let val = X::C;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xd() {
    let val = X::D;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xe() {
    let val = X::E;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xf() {
    let val = X::F;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xg() {
    let val = X::G;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xh() {
    let val = X::H;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xi() {
    let val = X::I;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xj() {
    let val = X::J;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xk() {
    let val = X::K;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xl() {
    let val = X::L;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xm() {
    let val = X::M;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xn() {
    let val = X::N;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xo() {
    let val = X::O;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xp() {
    let val = X::P;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xq() {
    let val = X::Q;

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}
