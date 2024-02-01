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

#[test]
fn serialize() {
    let t = trybuild::TestCases::new();

    t.pass("tests/ser/unit_struct.rs");
    t.pass("tests/ser/tuple_struct.rs");
    t.pass("tests/ser/named_field_struct.rs");

    t.pass("tests/ser/unit_enum.rs");
    t.pass("tests/ser/tuple_enum.rs");
    t.pass("tests/ser/named_field_enum.rs");

    t.pass("tests/ser/skip.rs");
    t.pass("tests/ser/skip_serializing.rs");

    t.pass("tests/ser/into_struct.rs");
    t.pass("tests/ser/into_enum.rs");
    t.pass("tests/ser/into_field.rs");

    t.pass("tests/ser/to_struct.rs");
    t.pass("tests/ser/to_enum.rs");
    t.pass("tests/ser/to_field.rs");

    t.pass("tests/ser/transparent.rs");

    t.pass("tests/ser/generics.rs");
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

    t.pass("tests/de/skip.rs");
    t.pass("tests/de/skip_deserializing.rs");
    t.pass("tests/de/default.rs");

    t.pass("tests/de/from_struct.rs");
    t.pass("tests/de/from_enum.rs");
    t.pass("tests/de/from_field.rs");

    t.pass("tests/de/try_from_struct.rs");
    t.pass("tests/de/try_from_enum.rs");
    t.pass("tests/de/try_from_field.rs");

    t.pass("tests/de/transparent.rs");

    t.pass("tests/de/generics.rs");
}
