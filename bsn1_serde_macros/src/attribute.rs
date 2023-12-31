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
}

impl Attribute {
    fn parse(attr: &syn::Attribute) -> syn::Result<Option<Self>> {
        let mut it = match &attr.meta {
            syn::Meta::List(meta) if meta.path.is_ident("bsn1_serde") => {
                meta.tokens.clone().into_iter()
            }
            _ => return Ok(None),
        };

        let ret = Self::default();

        while let Some(tt) = it.next() {
            match tt {
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
