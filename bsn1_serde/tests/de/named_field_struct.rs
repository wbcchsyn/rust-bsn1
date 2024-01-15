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

use bsn1_serde::{from_ber, from_der, to_ber, to_der};

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct A {}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde]
struct B {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set)]
struct C {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = UNIVERSAL)]
struct D {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_class = UNIVERSAL)]
struct E {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_pc = CONSTRUCTED)]
struct F {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_pc = CONSTRUCTED)]
struct G {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = UNIVERSAL, tag_pc = CONSTRUCTED)]
struct H {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_class = UNIVERSAL, tag_pc = CONSTRUCTED)]
struct I {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_num = 0)]
struct J {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_num = 1)]
struct K {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = UNIVERSAL, tag_num = 0x1e)]
struct L {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_class = UNIVERSAL, tag_num = 0x1f)]
struct M {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_pc = CONSTRUCTED, tag_num = 0x7f)]
struct N {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_pc = CONSTRUCTED, tag_num = 0x80)]
struct O {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(tag_class = UNIVERSAL, tag_pc = CONSTRUCTED, tag_num = 0x3fff)]
struct P {
    x: i32,
    y: String,
}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
#[bsn1_serde(id = Set, tag_class = UNIVERSAL, tag_pc = CONSTRUCTED, tag_num = 0x4000)]
struct Q {
    x: i32,
    y: String,
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
    test_m();
    test_n();
    test_o();
    test_p();
    test_q();
}

fn test_a() {
    let val = A {};

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_b() {
    let val = B {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_c() {
    let val = C {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_d() {
    let val = D {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_e() {
    let val = E {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_f() {
    let val = F {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_g() {
    let val = G {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_h() {
    let val = H {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_i() {
    let val = I {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_j() {
    let val = J {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_k() {
    let val = K {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_l() {
    let val = L {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_m() {
    let val = M {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_n() {
    let val = N {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_o() {
    let val = O {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_p() {
    let val = P {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_q() {
    let val = Q {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}
