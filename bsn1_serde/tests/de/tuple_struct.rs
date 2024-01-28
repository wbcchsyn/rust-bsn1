// Copyright 2023-2024 Shin Yoshida
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

use bsn1_serde::{from_ber, from_der, to_ber, to_der};

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct A();

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde()]
struct B(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean)]
struct C(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = CONTEXT_SPECIFIC)]
struct D(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean, tag_class = CONTEXT_SPECIFIC)]
struct E(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_pc = CONSTRUCTED)]
struct F(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean, tag_pc = CONSTRUCTED)]
struct G(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = CONTEXT_SPECIFIC, tag_pc = CONSTRUCTED)]
struct H(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean, tag_class = CONTEXT_SPECIFIC, tag_pc = CONSTRUCTED)]
struct I(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_num = 0)]
struct J(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean, tag_num = 1)]
struct K(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = CONTEXT_SPECIFIC, tag_num = 0x1e)]
struct L(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean, tag_class = CONTEXT_SPECIFIC, tag_num = 0x1f)]
struct M(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_pc = CONSTRUCTED, tag_num = 0x7f)]
struct N(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean, tag_pc = CONSTRUCTED, tag_num = 0x80)]
struct O(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = CONTEXT_SPECIFIC, tag_pc = CONSTRUCTED, tag_num = 0x3fff)]
struct P(i32, String);

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Boolean, tag_class = CONTEXT_SPECIFIC, tag_pc = CONSTRUCTED, tag_num = 0x4000)]
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
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_b() {
    let val = B(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_c() {
    let val = C(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_d() {
    let val = D(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_e() {
    let val = E(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_f() {
    let val = F(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_g() {
    let val = G(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_h() {
    let val = H(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_i() {
    let val = I(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_j() {
    let val = J(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_k() {
    let val = K(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_l() {
    let val = L(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_m() {
    let val = M(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_n() {
    let val = N(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_o() {
    let val = O(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_p() {
    let val = P(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_q() {
    let val = Q(123, "abc".to_string());

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}
