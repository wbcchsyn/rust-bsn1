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

use bsn1::{Ber, BerRef, IdRef};
use bsn1_serde::from_ber;

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct A {}

#[derive(bsn1_serde::Serialize, bsn1_serde::Deserialize, Debug, PartialEq)]
struct B {
    x: i32,
    y: bool,
}

fn main() {
    test_a();
    test_b();
}

fn test_a() {
    let val = A {};

    let eoc: &[u8] = BerRef::eoc().as_ref();
    let ber = unsafe { Ber::new_indefinite(IdRef::sequence(), eoc.into()) };
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_b() {
    let val = B { x: 123, y: true };

    let mut ber = unsafe { Ber::with_id_length_indefinite(IdRef::sequence(), 0) };
    ber.extend_from_slice(&Ber::from(val.x));
    ber.extend_from_slice(&Ber::from(val.y));
    ber.extend_from_slice(BerRef::eoc());
    assert_eq!(val, from_ber(&ber).unwrap());
}
