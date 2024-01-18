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

use bsn1_serde::ser::Serialize as _;
use bsn1_serde::to_der;

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct A {
    inner: String,
}

impl Into<String> for A {
    fn into(self) -> String {
        self.inner
    }
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct B {
    _dummy: i8,
    inner: String,
}

impl Into<String> for B {
    fn into(self) -> String {
        self.inner
    }
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct C(String);

impl Into<String> for C {
    fn into(self) -> String {
        self.0
    }
}

#[derive(bsn1_serde::Serialize, Clone)]
#[bsn1_serde(into = "String")]
struct D(String, i8);

impl Into<String> for D {
    fn into(self) -> String {
        self.0
    }
}

fn main() {
    test_a();
    test_b();
    test_c();
    test_d();
}

fn test_a() {
    let inner = "inner".to_string();
    let val = A {
        inner: inner.clone(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_b() {
    let inner = "inner".to_string();
    let val = B {
        _dummy: 10,
        inner: inner.clone(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_c() {
    let inner = "inner".to_string();
    let val = C(inner.clone());

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}

fn test_d() {
    let inner = "inner".to_string();
    let val = D(inner.clone(), 10);

    let der = to_der(&val).unwrap();
    assert_eq!(der, to_der(&inner).unwrap());
    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
}
