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

use crate::generics::Generics;
use crate::{Attribute, DataContainer};
use proc_macro2::{Ident, TokenStream};
use quote::quote;

#[allow(non_snake_case)]
pub fn do_serialize(ast: syn::DeriveInput) -> syn::Result<TokenStream> {
    let name = &ast.ident;

    let attribute = Attribute::try_from(&ast.attrs[..])?;
    attribute.sanitize_as_container()?;

    let generics = Generics::from(ast.generics);
    let idents = generics.idents();
    let ident_bounds = generics.ident_bounds();
    let where_clause = generics.where_clause();

    let methods = if let Some(ty) = attribute.into_type() {
        do_into_serialize(&ty)?
    } else if let Some(to_fn) = attribute.to_path() {
        do_to_serialize(&to_fn)?
    } else {
        match ast.data {
            syn::Data::Struct(data) => do_serialize_struct(attribute, &ast.ident, data)?,
            syn::Data::Enum(data) => do_serialize_enum(attribute, &ast.ident, data)?,
            syn::Data::Union(_) => {
                return Err(syn::Error::new_spanned(name, "Union is not supported."))
            }
        }
    };

    let Serialize = quote! { ::bsn1_serde::ser::Serialize };

    Ok(quote! {
        impl #ident_bounds  #Serialize for #name #idents
            #where_clause {
            #methods
        }
    })
}

#[allow(non_snake_case)]
fn do_into_serialize(ty: &syn::Path) -> syn::Result<TokenStream> {
    let Result = quote! { ::std::result::Result };
    let Option = quote! { ::std::option::Option };
    let Write = quote! { ?Sized + ::std::io::Write };
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

        fn der_contents_len(&self) -> #Result<#Option<usize>, #Error> {
            #Result::Ok(#Option::None)
        }
    })
}

#[allow(non_snake_case)]
fn do_to_serialize(to_fn: &syn::Path) -> syn::Result<TokenStream> {
    let Result = quote! { ::std::result::Result };
    let Option = quote! { ::std::option::Option };
    let Write = quote! { ?Sized + ::std::io::Write };
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

        fn der_contents_len(&self) -> #Result<#Option<usize>, #Error> {
            let this = #to_fn(self);
            #Serialize::der_contents_len(&this)
        }
    })
}

#[allow(non_snake_case)]
fn do_serialize_struct(
    attribute: Attribute,
    struct_name: &Ident,
    data: syn::DataStruct,
) -> syn::Result<TokenStream> {
    let Result = quote! { ::std::result::Result };
    let Option = quote! { ::std::option::Option };
    let Write = quote! { ?Sized + ::std::io::Write };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };

    let data = DataContainer::try_from((attribute, struct_name.clone(), data))?;
    let buffer = quote! { buffer };

    let (write_id, id_len, der_contents_len, write_der_contents) =
        if data.attribute().is_transparent() {
            (
                data.write_id_transparent(&buffer)?,
                data.id_len_transparent()?,
                data.der_contents_len_transparent()?,
                data.write_der_contents_transparent(&buffer)?,
            )
        } else {
            (
                data.write_id(&buffer)?,
                data.id_len()?,
                data.der_contents_len()?,
                data.write_der_contents(&buffer)?,
            )
        };

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

            fn der_contents_len(&self) -> #Result<#Option<usize>, #Error> {
                #der_contents_len
            }
    })
}

#[allow(non_snake_case)]
fn do_serialize_enum(
    attribute: Attribute,
    enum_name: &Ident,
    data: syn::DataEnum,
) -> syn::Result<TokenStream> {
    attribute.sanitize_as_enum()?;

    let Result = quote! { ::std::result::Result };
    let Option = quote! { ::std::option::Option };
    let Write = quote! { ?Sized + ::std::io::Write };
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

            fn der_contents_len(&self) -> #Result<#Option<usize>, #Error> {
                match self {
                    #(#arms =>  { #der_contents_lens } )*
                }
            }
    })
}
