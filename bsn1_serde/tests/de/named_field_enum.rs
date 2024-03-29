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
    A {},
    //#[bsn1_serde()]
    //B { x: i32, y: String },
    #[bsn1_serde(id = Set)]
    C {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_class = PRIVATE)]
    D {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_class = PRIVATE, id = Set)]
    E {
        x: i32,
        y: String,
    },
    //#[bsn1_serde(tag_pc = CONSTRUCTED)]
    //F { x: i32, y: String },
    //#[bsn1_serde(tag_pc = CONSTRUCTED, id = Set)]
    //G {
    //    x: i32,
    //    y: String,
    //},
    //#[bsn1_serde(tag_pc = CONSTRUCTED, tag_class = PRIVATE)]
    //H {
    //    x: i32,
    //    y: String,
    //},
    //#[bsn1_serde(tag_pc = CONSTRUCTED, tag_class = PRIVATE, id = Set)]
    //I {
    //    x: i32,
    //    y: String,
    //},
    #[bsn1_serde(tag_num = 0)]
    J {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 1, id = Set)]
    K {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x1e, tag_class = PRIVATE)]
    L {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x1f, tag_class = PRIVATE, id = Set)]
    M {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x7f, tag_pc = CONSTRUCTED)]
    N {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x80, tag_pc = CONSTRUCTED, id = Set)]
    O {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x3fff, tag_pc = CONSTRUCTED, tag_class = PRIVATE)]
    P {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x4000, tag_pc = CONSTRUCTED, tag_class = PRIVATE, id = Set)]
    Q {
        x: i32,
        y: String,
    },
}

fn main() {
    test_xa();
    //test_xb();
    test_xc();
    test_xd();
    test_xe();
    //test_xf();
    //test_xg();
    //test_xh();
    //test_xi();
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
    let val = X::A {};

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xc() {
    let val = X::C {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xd() {
    let val = X::D {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xe() {
    let val = X::E {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xj() {
    let val = X::J {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xk() {
    let val = X::K {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xl() {
    let val = X::L {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xm() {
    let val = X::M {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xn() {
    let val = X::N {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xo() {
    let val = X::O {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xp() {
    let val = X::P {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}

fn test_xq() {
    let val = X::Q {
        x: 123,
        y: "abc".to_string(),
    };

    let der = to_der(&val).unwrap();
    assert_eq!(val, from_der(&der).unwrap());

    let ber = to_ber(&val).unwrap();
    assert_eq!(val, from_ber(&ber).unwrap());
}
