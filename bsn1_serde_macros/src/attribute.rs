// Copyright 2023 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of bsn1_serde_macros
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

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::{quote, ToTokens};

struct AttrArgument<T> {
    val: T,
    ident: Ident,
}

#[derive(Default)]
pub struct Attribute {
    // Arguments about Identifier for struct and variant.
    // Exclusive with arguments about skip and about conversion.
    id_: Option<AttrArgument<u8>>,
    tag_class: Option<AttrArgument<u8>>,
    tag_pc: Option<AttrArgument<u8>>,
    tag_num: Option<AttrArgument<u128>>,

    // Arguments about skip for field.
    // Exclusive with arguments about identifier and about conversion.
    skip_serialzing: Option<AttrArgument<()>>,
    skip_deserialzing: Option<AttrArgument<()>>,
    default: Option<AttrArgument<syn::Path>>,
    skip: Option<AttrArgument<()>>,

    // Arguments about conversion for struct, enum, and field.
    // Exclusive with arguments about identifier and about skip.
    //
    // `into` and `to` are exclusive.
    // `from` and `try_from` are exclusive.
    into: Option<AttrArgument<syn::Path>>,
    from: Option<AttrArgument<syn::Path>>,
    to: Option<AttrArgument<syn::Path>>,
    try_from: Option<AttrArgument<syn::Path>>,
}

impl TryFrom<&[syn::Attribute]> for Attribute {
    type Error = syn::Error;

    fn try_from(attrs: &[syn::Attribute]) -> syn::Result<Self> {
        let mut ret = None;

        for attr in attrs {
            if let Some(a) = Self::parse(attr)? {
                match ret {
                    None => ret = Some(a),
                    Some(_) => error(attr, "Duplicated `bsn1_serde` attribute.")?,
                }
            }
        }

        if let Some(ref attr) = ret {
            attr.sanitize()?;
        }
        Ok(ret.unwrap_or_default())
    }
}

impl Attribute {
    fn parse(attr: &syn::Attribute) -> syn::Result<Option<Self>> {
        let mut it = match &attr.meta {
            syn::Meta::List(meta) if meta.path.is_ident("bsn1_serde") => {
                meta.tokens.clone().into_iter()
            }
            _ => return Ok(None),
        };

        let mut ret = Self::default();

        while let Some(tt) = it.next() {
            match tt {
                TokenTree::Ident(ident) if ident == "id" => {
                    if ret.id_.is_some() {
                        error(&ident, "Duplicated `id` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.id_ = Some(AttrArgument {
                        val: parse_id_value(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "tag_class" => {
                    if ret.tag_class.is_some() {
                        error(&ident, "Duplicated `tag_class` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.tag_class = Some(AttrArgument {
                        val: parse_tag_class_value(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "tag_pc" => {
                    if ret.tag_pc.is_some() {
                        error(&ident, "Duplicated `tag_pc` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.tag_pc = Some(AttrArgument {
                        val: parse_tag_pc_value(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "tag_num" => {
                    if ret.tag_num.is_some() {
                        error(&ident, "Duplicated `tag_num` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.tag_num = Some(AttrArgument {
                        val: parse_tag_num_value(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "skip_serializing" => {
                    if ret.skip_serialzing.is_some() {
                        error(&ident, "Duplicated `skip_serializing` attribute.")?;
                    }
                    ret.skip_serialzing = Some(AttrArgument { val: (), ident })
                }
                TokenTree::Ident(ident) if ident == "skip_deserializing" => {
                    if ret.skip_deserialzing.is_some() {
                        error(&ident, "Duplicated `skip_deserializing` attribute.")?;
                    }
                    ret.skip_deserialzing = Some(AttrArgument { val: (), ident });
                }
                TokenTree::Ident(ident) if ident == "default" => {
                    if ret.default.is_some() {
                        error(&ident, "Duplicated `default` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.default = Some(AttrArgument {
                        val: parse_path(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "skip" => {
                    if ret.skip.is_some() {
                        error(&ident, "Duplicated `skip` attribute.")?;
                    }
                    ret.skip = AttrArgument { val: (), ident }.into();
                }
                TokenTree::Ident(ident) if ident == "into" => {
                    if ret.into.is_some() {
                        error(&ident, "Duplicated `into` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.into = Some(AttrArgument {
                        val: parse_path(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "from" => {
                    if ret.from.is_some() {
                        error(&ident, "Duplicated `from` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.from = Some(AttrArgument {
                        val: parse_path(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "to" => {
                    if ret.to.is_some() {
                        error(&ident, "Duplicated `to` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.to = Some(AttrArgument {
                        val: parse_path(&value)?,
                        ident,
                    });
                }
                TokenTree::Ident(ident) if ident == "try_from" => {
                    if ret.try_from.is_some() {
                        error(&ident, "Duplicated `try_from` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.try_from = Some(AttrArgument {
                        val: parse_path(&value)?,
                        ident,
                    });
                }
                TokenTree::Punct(punct) if punct.as_char() == ',' => continue,
                _ => error(tt, "Unexpected token.")?,
            }
        }

        Ok(Some(ret))
    }

    fn sanitize(&self) -> syn::Result<()> {
        macro_rules! exclusive {
            ($a: ident, $b: ident) => {
                if self.$a.is_some() && self.$b.is_some() {
                    let a = self.$a.as_ref().unwrap();
                    let b = self.$b.as_ref().unwrap();
                    error(
                        &a.ident,
                        format!(
                            "The arguemnt `{}` and `{}` are exclusive.",
                            a.ident, b.ident
                        ),
                    )?;
                }
            };
        }

        macro_rules! loop_exclusive {
            ([$a: ident], [$b: ident]) => {
                exclusive!($a, $b);
            };
            ([$a: ident], [$b: ident, $($b_: ident),+]) => {
                exclusive!($a, $b);
                loop_exclusive!([$a], [$($b_),+]);
            };
            ([$a: ident, $($a_: ident),+], [$($b: ident),+]) => {
                loop_exclusive!([$a], [$($b),+]);
                loop_exclusive!([$($a_),+], [$($b),+]);
            };
        }

        loop_exclusive!(
            [id_, tag_class, tag_pc, tag_num],
            [skip_serialzing, skip_deserialzing, skip, default]
        );
        loop_exclusive!(
            [id_, tag_class, tag_pc, tag_num],
            [into, from, to, try_from]
        );
        loop_exclusive!(
            [skip_serialzing, skip_deserialzing, skip, default],
            [into, from, to, try_from]
        );

        exclusive!(from, try_from);
        exclusive!(into, to);

        Ok(())
    }

    pub fn id(&self, default_id: u8) -> Option<TokenStream> {
        if self.id_.is_none()
            && self.tag_class.is_none()
            && self.tag_pc.is_none()
            && self.tag_num.is_none()
        {
            return None;
        }

        let mut octets: Vec<u8> = Vec::new();

        match self.id_ {
            Some(ref arg) => octets.push(arg.val),
            None => octets.push(default_id),
        };

        if let Some(ref arg) = self.tag_class {
            const MASK: u8 = 0x3f;
            octets[0] = (octets[0] & MASK) | arg.val;
        }

        if let Some(ref arg) = self.tag_pc {
            const MASK: u8 = 0xdf;
            octets[0] = (octets[0] & MASK) | arg.val;
        }

        if let Some(ref arg) = self.tag_num {
            let mut tag_num = arg.val;
            const LONG_FORM: u8 = 0x1f;

            if tag_num < LONG_FORM as u128 {
                const MASK: u8 = 0xe0;
                octets[0] = (octets[0] & MASK) | tag_num as u8;
            } else {
                octets[0] |= LONG_FORM;

                while 0 < tag_num {
                    octets.push((tag_num % 0x80) as u8);
                    tag_num /= 0x80;
                }

                for i in 2..octets.len() {
                    octets[i] |= 0x80;
                }

                octets[1..].reverse();
            }
        }

        Some(quote! { [#(#octets),*] })
    }

    pub fn is_skip_serializing(&self) -> bool {
        self.skip.is_some() || self.skip_serialzing.is_some()
    }

    pub fn is_skip_deserializing(&self) -> bool {
        self.skip.is_some() || self.skip_deserialzing.is_some()
    }

    pub fn default_path(&self) -> syn::Path {
        match self.default {
            Some(ref arg) => arg.val.clone(),
            None => syn::parse_str::<syn::Path>("Default::default").unwrap(),
        }
    }

    pub fn into_type(&self) -> Option<&syn::Path> {
        self.into.as_ref().map(|arg| &arg.val)
    }

    pub fn from_type(&self) -> Option<&syn::Path> {
        self.from.as_ref().map(|arg| &arg.val)
    }

    pub fn to_path(&self) -> Option<&syn::Path> {
        self.to.as_ref().map(|arg| &arg.val)
    }

    pub fn try_from_type(&self) -> Option<&syn::Path> {
        self.try_from.as_ref().map(|arg| &arg.val)
    }
}

fn error<T: ToTokens, U: std::fmt::Display>(tt: T, message: U) -> syn::Result<()> {
    Err(syn::Error::new_spanned(tt, message))
}

fn take_value(
    ident: &syn::Ident,
    eq: Option<TokenTree>,
    val: Option<TokenTree>,
) -> syn::Result<TokenTree> {
    match eq {
        Some(TokenTree::Punct(punct)) if punct.as_char() == '=' => (),
        _ => error(ident, format!("Expected `=` after `{}`.", ident))?,
    }

    val.ok_or(syn::Error::new_spanned(
        ident,
        format!("Expected value after `{} =`.", ident),
    ))
}

fn parse_id_value(value: &TokenTree) -> syn::Result<u8> {
    // Limit the values for now.
    // (It is easy to extend the values later.)
    const VALUES: &[(&str, u8)] = &[
        ("EOC", 0x00),
        ("Boolean", 0x01),
        ("Integer", 0x02),
        ("BitString", 0x03),
        ("OctetString", 0x04),
        ("Null", 0x05),
        ("Real", 0x09),
        ("UTF8String", 0x0c),
        ("Sequence", 0x30),
        ("Set", 0x31),
    ];

    let values: Vec<&'static str> = VALUES.iter().map(|(s, _)| *s).collect();
    let values = values.join(", ");
    let error_message = format!("Expected one of [{}].", values);

    let ident = match value {
        TokenTree::Ident(ident) => ident,
        _ => return Err(syn::Error::new_spanned(value, error_message)),
    };

    for &(s, v) in VALUES {
        if ident == s {
            return Ok(v);
        }
    }

    Err(syn::Error::new_spanned(value, error_message))
}

fn parse_tag_class_value(value: &TokenTree) -> syn::Result<u8> {
    const VALUES: &[(&str, u8)] = &[
        ("UNIVERSAL", 0x00),
        ("APPLICATION", 0x40),
        ("CONTEXT_SPECIFIC", 0x80),
        ("PRIVATE", 0xc0),
    ];

    let values: Vec<&'static str> = VALUES.iter().map(|(s, _)| *s).collect();
    let values = values.join(", ");
    let error_message = format!("Expected one of [{}].", values);

    let ident = match value {
        TokenTree::Ident(ident) => ident,
        _ => return Err(syn::Error::new_spanned(value, error_message)),
    };

    for &(s, v) in VALUES {
        if ident == s {
            return Ok(v);
        }
    }

    Err(syn::Error::new_spanned(value, error_message))
}

fn parse_tag_pc_value(value: &TokenTree) -> syn::Result<u8> {
    const VALUES: &[(&str, u8)] = &[("PRIMITIVE", 0x00), ("CONSTRUCTED", 0x20)];

    let values: Vec<&'static str> = VALUES.iter().map(|(s, _)| *s).collect();
    let values = values.join(", ");
    let error_message = format!("Expected one of [{}].", values);

    let ident = match value {
        TokenTree::Ident(ident) => ident,
        _ => return Err(syn::Error::new_spanned(value, error_message)),
    };

    for &(s, v) in VALUES {
        if ident == s {
            return Ok(v);
        }
    }

    Err(syn::Error::new_spanned(value, error_message))
}

fn parse_tag_num_value(value: &TokenTree) -> syn::Result<u128> {
    match value {
        TokenTree::Literal(literal) => {
            let val = literal.to_string();
            let val = if val.starts_with("+") {
                &val["+".len()..]
            } else {
                &val
            };

            const PREFIXES: &[(&str, u32)] = &[
                ("0b", 2),
                ("0B", 2),
                ("0o", 8),
                ("0O", 8),
                ("0x", 16),
                ("0X", 16),
                ("", 10),
            ];
            for &(prefix, radix) in PREFIXES {
                if val.starts_with(prefix) {
                    let val = &val[prefix.len()..];
                    return u128::from_str_radix(val, radix).map_err(|_| {
                        syn::Error::new_spanned(value, "Expected literal valid as u128.")
                    });
                }
            }

            unreachable!();
        }
        _ => Err(syn::Error::new_spanned(
            value,
            "Expected literal valid as u128.",
        )),
    }
}

fn parse_path(path: &TokenTree) -> syn::Result<syn::Path> {
    match path {
        TokenTree::Literal(path) => {
            let path = path.to_string();
            let path = path.trim_matches('"');
            syn::parse_str::<syn::Path>(path)
        }
        _ => Err(syn::Error::new_spanned(
            path,
            "Expected literal string valid as path.",
        )),
    }
}
