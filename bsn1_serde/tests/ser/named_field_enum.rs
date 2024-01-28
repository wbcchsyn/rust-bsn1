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

use bsn1::{ClassTag, Contents, DerRef, IdRef, PCTag};
use bsn1_serde::ser::Serialize as _;
use bsn1_serde::to_der;

#[derive(bsn1_serde::Serialize)]
enum X {
    A {},
    #[bsn1_serde()]
    B {
        x: i32,
        y: String,
    },
    #[bsn1_serde(id = EOC)]
    C {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_class = APPLICATION)]
    D {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_class = APPLICATION, id = EOC)]
    E {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_pc = PRIMITIVE)]
    F {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_pc = PRIMITIVE, id = EOC)]
    G {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_pc = PRIMITIVE, tag_class = APPLICATION)]
    H {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_pc = PRIMITIVE, tag_class = APPLICATION, id = EOC)]
    I {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0)]
    J {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 1, id = EOC)]
    K {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x1e, tag_class = APPLICATION)]
    L {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x1f, tag_class = APPLICATION, id = EOC)]
    M {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x7f, tag_pc = PRIMITIVE)]
    N {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x80, tag_pc = PRIMITIVE, id = EOC)]
    O {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x3fff, tag_pc = PRIMITIVE, tag_class = APPLICATION)]
    P {
        x: i32,
        y: String,
    },
    #[bsn1_serde(tag_num = 0x4000, tag_pc = PRIMITIVE, tag_class = APPLICATION, id = EOC)]
    Q {
        x: i32,
        y: String,
    },
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
    let val = X::A {};
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id(), IdRef::sequence());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    assert_eq!(der.contents().len(), 0);
}

fn test_xb() {
    let val = X::B {
        x: 315,
        y: "foo".to_string(),
    };
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
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xc() {
    let val = X::C {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::eoc().class());
    assert_eq!(der.id().pc(), IdRef::eoc().pc());
    assert_eq!(der.id().number().unwrap(), IdRef::eoc().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xd() {
    let val = X::D {
        x: 315,
        y: "foo".to_string(),
    };
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
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xe() {
    let val = X::E {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::eoc().pc());
    assert_eq!(der.id().number().unwrap(), IdRef::eoc().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xf() {
    let val = X::F {
        x: 315,
        y: "foo".to_string(),
    };
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
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xg() {
    let val = X::G {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::eoc().class());
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), IdRef::eoc().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xh() {
    let val = X::H {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(
        der.id().number().unwrap(),
        IdRef::sequence().number().unwrap()
    );

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xi() {
    let val = X::I {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), IdRef::eoc().number().unwrap());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xj() {
    let val = X::J {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xk() {
    let val = X::K {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::eoc().class());
    assert_eq!(der.id().pc(), IdRef::eoc().pc());
    assert_eq!(der.id().number().unwrap(), 1_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xl() {
    let val = X::L {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::sequence().pc());
    assert_eq!(der.id().number().unwrap(), 0x1e_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xm() {
    let val = X::M {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), IdRef::eoc().pc());
    assert_eq!(der.id().number().unwrap(), 0x1f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xn() {
    let val = X::N {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::sequence().class());
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x7f_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xo() {
    let val = X::O {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), IdRef::eoc().class());
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x80_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xp() {
    let val = X::P {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x3fff_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}

fn test_xq() {
    let val = X::Q {
        x: 315,
        y: "foo".to_string(),
    };
    let der = to_der(&val).unwrap();

    assert_eq!(der.id().len(), val.id_len().unwrap());
    assert_eq!(der.id().class(), ClassTag::Application);
    assert_eq!(der.id().pc(), PCTag::Primitive);
    assert_eq!(der.id().number().unwrap(), 0x4000_u32.into());

    assert_eq!(der.length().definite().unwrap(), der.contents().len());

    assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
    {
        let contents = der.contents();
        let mut contents: &[u8] = contents.as_ref();

        let der0 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der0.id(), IdRef::integer());
        assert_eq!(der0.contents(), &Contents::from(315_i32));

        let der1 = DerRef::parse(&mut contents).unwrap();
        assert_eq!(der1.id(), IdRef::utf8_string());
        assert_eq!(der1.contents(), &Contents::from("foo"));

        assert_eq!(contents.is_empty(), true);
    }
}
