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

use proc_macro2::TokenTree;
use quote::ToTokens;

#[derive(Default)]
pub struct Attribute {
    id_: Option<u8>,
    tag_class: Option<u8>,
    tag_pc: Option<u8>,
    tag_num: Option<u128>,
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
                    ret.id_ = Some(parse_id_value(&value)?);
                }
                TokenTree::Ident(ident) if ident == "tag_class" => {
                    if ret.tag_class.is_some() {
                        error(&ident, "Duplicated `tag_class` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.tag_class = Some(parse_tag_class_value(&value)?);
                }
                TokenTree::Ident(ident) if ident == "tag_pc" => {
                    if ret.tag_pc.is_some() {
                        error(&ident, "Duplicated `tag_pc` attribute.")?;
                    }
                    let value = take_value(&ident, it.next(), it.next())?;
                    ret.tag_pc = Some(parse_tag_pc_value(&value)?);
                }
                TokenTree::Punct(punct) if punct.as_char() == ',' => continue,
                _ => error(tt, "Unexpected token.")?,
            }
        }

        Ok(Some(ret))
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
