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

use crate::{Attribute, DataContainer};
use proc_macro2::TokenStream;
use quote::quote;

pub fn do_deserialize(ast: syn::DeriveInput) -> syn::Result<TokenStream> {
    let name = &ast.ident;
    let attribute = Attribute::try_from(&ast.attrs[..])?;

    let methods = match ast.data {
        syn::Data::Struct(data) => do_deserialize_struct(attribute, data)?,
        syn::Data::Enum(data) => do_deserialize_enum(attribute, data)?,
        _ => return Err(syn::Error::new_spanned(ast, "Only struct or enum is supported.").into()),
    };

    Ok(quote! {
        impl ::bsn1_serde::de::Deserialize for #name {
            #methods
        }
    })
}

#[allow(non_snake_case)]
fn do_deserialize_struct(attribute: Attribute, data: syn::DataStruct) -> syn::Result<TokenStream> {
    let IdRef = quote! { ::bsn1_serde::macro_alias::IdRef };
    let Length = quote! { ::bsn1_serde::macro_alias::Length };
    let ContentsRef = quote! { ::bsn1_serde::macro_alias::ContentsRef };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };

    let Result = quote! { ::std::result::Result };

    let data = DataContainer::try_from((attribute, data))?;
    let id = quote! { id };
    let contents = quote! { contents };
    let from_der = data.from_der(&id, &contents)?;

    Ok(quote! {
        unsafe fn from_ber(id: &#IdRef, length: #Length, contents: &#ContentsRef)
            -> #Result<Self, #Error> {
            todo!()
        }

        fn from_der(id: &#IdRef, contents: &#ContentsRef) -> #Result<Self, #Error> {
            #from_der
        }
    })
}

#[allow(non_snake_case)]
fn do_deserialize_enum(_attribute: Attribute, _data: syn::DataEnum) -> syn::Result<TokenStream> {
    let IdRef = quote! { ::bsn1_serde::macro_alias::IdRef };
    let Length = quote! { ::bsn1_serde::macro_alias::Length };
    let ContentsRef = quote! { ::bsn1_serde::macro_alias::ContentsRef };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };

    let Result = quote! { ::std::result::Result };

    Ok(quote! {
        unsafe fn from_ber(id: &#IdRef, length: #Length, contents: &#ContentsRef)
            -> #Result<Self, #Error> {
            todo!()
        }

        fn from_der(id: &#IdRef, contents: &#ContentsRef) -> #Result<Self, #Error> {
            todo!()
        }
    })
}
