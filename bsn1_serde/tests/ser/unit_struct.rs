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
struct A;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde]
struct B;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer)]
struct C;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = APPLICATION)]
struct D;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_class = APPLICATION)]
struct E;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_pc = CONSTRUCTED)]
struct F;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_pc = CONSTRUCTED)]
struct G;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = APPLICATION, tag_pc = CONSTRUCTED)]
struct H;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_class = APPLICATION, tag_pc = CONSTRUCTED)]
struct I;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_num = 0)]
struct J;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_num = 1)]
struct K;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = APPLICATION, tag_num = 0x1e)]
struct L;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_class = APPLICATION, tag_num = 0x1f)]
struct M;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_pc = CONSTRUCTED, tag_num = 0x7f)]
struct N;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(id = Integer, tag_pc = CONSTRUCTED, tag_num = 0x80)]
struct O;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(tag_class = APPLICATION, tag_pc = CONSTRUCTED, tag_num = 0x3fff)]
struct P;

#[derive(bsn1_serde::Serialize)]
#[bsn1_serde(
    id = Integer,
    tag_class = APPLICATION,
    tag_pc = CONSTRUCTED,
    tag_num = 0x4000)]
struct Q;

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
    let val = A;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id(), IdRef::sequence());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_b() {
    let val = B;
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
    let val = C;
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
    assert_eq!(der.contents().len(), 0);
}

fn test_d() {
    let val = D;
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
    assert_eq!(der.contents().len(), 0);
}

fn test_e() {
    let val = E;
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
    assert_eq!(der.contents().len(), 0);
}

fn test_f() {
    let val = F;
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
    let val = G;
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
    assert_eq!(der.contents().len(), 0);
}

fn test_h() {
    let val = H;
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
    assert_eq!(der.contents().len(), 0);
}

fn test_i() {
    let val = I;
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
    assert_eq!(der.contents().len(), 0);
}

fn test_j() {
    let val = J;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_k() {
    let val = K;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::integer().class());
    assert_eq!(der.id().pc(), IdRef::integer().pc());
    assert_eq!(der.id().number().unwrap(), 1_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_l() {
    let val = L;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0x1e_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_m() {
    let val = M;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::integer().pc());
    assert_eq!(der.id().number().unwrap(), 0x1f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_n() {
    let val = N;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x7f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_o() {
    let val = O;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::integer().class());
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x80_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_p() {
    let val = P;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x3fff_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_q() {
    let val = Q;
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Constructed);
    assert_eq!(der.id().number().unwrap(), 0x4000_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}
