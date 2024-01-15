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

#[test]
fn serialize() {
    let t = trybuild::TestCases::new();

    t.pass("tests/ser/unit_struct.rs");
    t.pass("tests/ser/tuple_struct.rs");
    t.pass("tests/ser/named_field_struct.rs");

    t.pass("tests/ser/unit_enum.rs");
    t.pass("tests/ser/tuple_enum.rs");
    t.pass("tests/ser/named_field_enum.rs");
}

#[test]
fn deserialize() {
    let t = trybuild::TestCases::new();

    t.pass("tests/de/unit_struct.rs");
    t.pass("tests/de/tuple_struct.rs");
    t.pass("tests/de/named_field_struct.rs");

    t.pass("tests/de/unit_enum.rs");
    t.pass("tests/de/tuple_enum.rs");
    t.pass("tests/de/named_field_enum.rs");

    t.pass("tests/de/indefinite_length.rs");
}