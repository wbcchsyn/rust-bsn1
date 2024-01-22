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
use proc_macro2::{Ident, TokenStream};
use quote::quote;

#[allow(non_snake_case)]
pub fn do_serialize(ast: syn::DeriveInput) -> syn::Result<TokenStream> {
    let name = &ast.ident;

    let attribute = Attribute::try_from(&ast.attrs[..])?;
    attribute.sanitize_as_container()?;

    let methods = if let Some(ty) = attribute.into_type() {
        do_into_serialize(&ty)?
    } else if let Some(to_fn) = attribute.to_path() {
        do_to_serialize(&to_fn)?
    } else {
        match ast.data {
            syn::Data::Struct(data) => do_serialize_struct(attribute, data)?,
            syn::Data::Enum(data) => do_serialize_enum(attribute, &ast.ident, data)?,
            syn::Data::Union(_) => {
                return Err(syn::Error::new_spanned(name, "Union is not supported."))
            }
        }
    };

    let Serialize = quote! { ::bsn1_serde::ser::Serialize };

    Ok(quote! {
        impl #Serialize for #name {
            #methods
        }
    })
}

#[allow(non_snake_case)]
fn do_into_serialize(ty: &syn::Path) -> syn::Result<TokenStream> {
    let Result = quote! { ::std::result::Result };
    let Write = quote! { ::std::io::Write };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };
    let Clone = quote! { ::std::clone::Clone };
    let Into = quote! { ::std::convert::Into };
    let Serialize = quote! { ::bsn1_serde::ser::Serialize };

    Ok(quote! {
        fn write_id<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
            let this: Self = #Clone::clone(self);
            let this: #ty = #Into::into(this);
            #Serialize::write_id(&this, buffer)
        }

        fn write_der_contents<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
            let this: Self = #Clone::clone(self);
            let this: #ty = #Into::into(this);
            #Serialize::write_der_contents(&this, buffer)
        }

        fn id_len(&self) -> #Result<usize, #Error> {
            let this: Self = #Clone::clone(self);
            let this: #ty = #Into::into(this);
            #Serialize::id_len(&this)
        }

        fn der_contents_len(&self) -> #Result<usize, #Error> {
            let this: Self = #Clone::clone(self);
            let this: #ty = #Into::into(this);
            #Serialize::der_contents_len(&this)
        }
    })
}

#[allow(non_snake_case)]
fn do_to_serialize(to_fn: &syn::Path) -> syn::Result<TokenStream> {
    let Result = quote! { ::std::result::Result };
    let Write = quote! { ::std::io::Write };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };
    let Serialize = quote! { ::bsn1_serde::ser::Serialize };

    Ok(quote! {
        fn write_id<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
            let this = #to_fn(self);
            #Serialize::write_id(&this, buffer)
        }

        fn write_der_contents<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
            let this = #to_fn(self);
            #Serialize::write_der_contents(&this, buffer)
        }

        fn id_len(&self) -> #Result<usize, #Error> {
            let this = #to_fn(self);
            #Serialize::id_len(&this)
        }

        fn der_contents_len(&self) -> #Result<usize, #Error> {
            let this = #to_fn(self);
            #Serialize::der_contents_len(&this)
        }
    })
}

#[allow(non_snake_case)]
fn do_serialize_struct(attribute: Attribute, data: syn::DataStruct) -> syn::Result<TokenStream> {
    let Result = quote! { ::std::result::Result };
    let Write = quote! { ::std::io::Write };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };

    let data = DataContainer::try_from((attribute, data))?;
    let buffer = quote! { buffer };
    let write_id = data.write_id(&buffer)?;
    let id_len = data.id_len()?;
    let der_contents_len = data.der_contents_len()?;
    let write_der_contents = data.write_der_contents(&buffer)?;

    Ok(quote! {
            fn write_id<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
                #write_id
            }

            fn write_der_contents<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
                #write_der_contents
            }

            fn id_len(&self) -> #Result<usize, #Error> {
                #id_len
            }

            fn der_contents_len(&self) -> #Result<usize, #Error> {
                #der_contents_len
            }
    })
}

#[allow(non_snake_case)]
fn do_serialize_enum(
    _attribute: Attribute,
    enum_name: &Ident,
    data: syn::DataEnum,
) -> syn::Result<TokenStream> {
    let Result = quote! { ::std::result::Result };
    let Write = quote! { ::std::io::Write };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };

    let mut variants: Vec<DataContainer> = Vec::new();
    for variant in data.variants {
        variants.push(DataContainer::try_from((enum_name.clone(), variant))?);
    }

    let buffer = quote! { buffer };
    let mut arms: Vec<TokenStream> = Vec::new();
    let mut write_ids: Vec<TokenStream> = Vec::new();
    let mut id_lens: Vec<TokenStream> = Vec::new();
    let mut der_contents_lens: Vec<TokenStream> = Vec::new();
    let mut write_der_contentses: Vec<TokenStream> = Vec::new();

    for variant in variants.iter() {
        unsafe { arms.push(variant.to_match_arm()?) };
        write_ids.push(variant.write_id(&buffer)?);
        id_lens.push(variant.id_len()?);
        der_contents_lens.push(variant.der_contents_len()?);
        write_der_contentses.push(variant.write_der_contents(&buffer)?);
    }

    Ok(quote! {
            fn write_id<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
                match self {
                    #(#arms =>  { #write_ids } )*
                }
            }

            fn write_der_contents<W: #Write>(&self, buffer: &mut W) -> #Result<(), #Error> {
                match self {
                    #(#arms =>  { #write_der_contentses } )*
                }
            }

            fn id_len(&self) -> #Result<usize, #Error> {
                match self {
                    #(#arms =>  { #id_lens } )*
                }
            }

            fn der_contents_len(&self) -> #Result<usize, #Error> {
                match self {
                    #(#arms =>  { #der_contents_lens } )*
                }
            }
    })
}
