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

use bsn1_serde::de::Deserialize;
use bsn1_serde::ser::Serialize;
use bsn1_serde::{from_der, to_der};

#[derive(Debug, PartialEq, Eq, bsn1_serde::Serialize, bsn1_serde::Deserialize)]
enum X<A, B: Clone + Copy + Serialize + Deserialize>
where
    A: Serialize + Deserialize,
{
    #[bsn1_serde(id = Sequence)]
    Y { a: A },
    #[bsn1_serde(id = Set)]
    Z(B),
}

fn main() {
    test_xy();
    test_xz();
}

fn test_xy() {
    let a = true;
    let val = X::Y { a };

    let der = to_der(&val).unwrap();
    let val2: X<bool, i32> = from_der(&der).unwrap();
    assert_eq!(val, val2);
}

fn test_xz() {
    let b = 32;

    let val = X::Z(b);

    let der = to_der(&val).unwrap();
    let val2: X<bool, i32> = from_der(&der).unwrap();
    assert_eq!(val, val2);
}
