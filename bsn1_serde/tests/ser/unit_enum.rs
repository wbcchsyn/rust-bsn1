// Copyright 2023 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of bsn1_serde
//
//  bsn1_serde is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  bsn1_serde is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with bsn1_serde.  If not, see <http://www.gnu.org/licenses/>.
//
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use bsn1::{ClassTag, IdRef, PCTag};
use bsn1_serde::ser::Serialize as _;
use bsn1_serde::to_der;

#[derive(bsn1_serde::Serialize)]
enum X {
    A,
    #[bsn1_serde()]
    B,
    #[bsn1_serde(id = Set)]
    C,
    #[bsn1_serde(tag_class = UNIVERSAL)]
    D,
    #[bsn1_serde(tag_class = UNIVERSAL, id = Set)]
    E,
    #[bsn1_serde(tag_pc = PRIMITIVE)]
    F,
    #[bsn1_serde(tag_pc = PRIMITIVE, id = Set)]
    G,
    #[bsn1_serde(tag_pc = PRIMITIVE, tag_class = UNIVERSAL)]
    H,
    #[bsn1_serde(tag_pc = PRIMITIVE, tag_class = UNIVERSAL, id = Set)]
    I,
    #[bsn1_serde(tag_num = 0)]
    J,
    #[bsn1_serde(tag_num = 1, id = Set)]
    K,
    #[bsn1_serde(tag_num = 0x1e, tag_class = UNIVERSAL)]
    L,
    #[bsn1_serde(tag_num = 0x1f, tag_class = UNIVERSAL, id = Set)]
    M,
    #[bsn1_serde(tag_num = 0x7f, tag_pc = PRIMITIVE)]
    N,
    #[bsn1_serde(tag_num = 0x80, tag_pc = PRIMITIVE, id = Set)]
    O,
    #[bsn1_serde(tag_num = 0x3fff, tag_pc = PRIMITIVE, tag_class = UNIVERSAL)]
    P,
    #[bsn1_serde(tag_num = 0x4000, tag_pc = PRIMITIVE, tag_class = UNIVERSAL, id = Set)]
    Q,
}

fn main() {
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
    test_xm();
    test_xn();
    test_xo();
    test_xp();
    test_xq();
}

fn test_xa() {
    let val = X::A;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id(), IdRef::sequence());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xb() {
    let val = X::B;
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

fn test_xc() {
    let val = X::C;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xd() {
    let val = X::D;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xe() {
    let val = X::E;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xf() {
    let val = X::F;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xg() {
    let val = X::G;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xh() {
    let val = X::H;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xi() {
    let val = X::I;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), IdRef::set().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xj() {
    let val = X::J;
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
    let val = X::K;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), 1_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xl() {
    let val = X::L;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0x1e_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xm() {
    let val = X::M;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), IdRef::set().pc());
    assert_eq!(der.id().number().unwrap(), 0x1f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xn() {
    let val = X::N;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x7f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xo() {
    let val = X::O;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::set().class());
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x80_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xp() {
    let val = X::P;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x3fff_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xq() {
    let val = X::Q;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Universal);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x4000_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}
