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
pub fn do_deserialize(ast: syn::DeriveInput) -> syn::Result<TokenStream> {
    let name = &ast.ident;

    let attribute = Attribute::try_from(&ast.attrs[..])?;
    attribute.sanitize_as_container()?;

    let generics = Generics::from(ast.generics);
    let idents = generics.idents();
    let ident_bounds = generics.ident_bounds();
    let where_clause = generics.where_clause();

    let methods = if let Some(ty) = attribute.from_type() {
        do_from_deserialize(ty)?
    } else if let Some(ty) = attribute.try_from_type() {
        do_try_from_deserialize(ty)?
    } else {
        match ast.data {
            syn::Data::Struct(data) => do_deserialize_struct(attribute, data)?,
            syn::Data::Enum(data) => do_deserialize_enum(attribute, &ast.ident, data)?,
            _ => {
                return Err(
                    syn::Error::new_spanned(name, "Only struct or enum is supported.").into(),
                )
            }
        }
    };

    let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

    Ok(quote! {
        impl #ident_bounds #Deserialize for #name #idents
            #where_clause {
            #methods
        }
    })
}

#[allow(non_snake_case)]
fn do_from_deserialize(ty: &syn::Path) -> syn::Result<TokenStream> {
    let IdRef = quote! { ::bsn1_serde::macro_alias::IdRef };
    let Length = quote! { ::bsn1_serde::macro_alias::Length };
    let ContentsRef = quote! { ::bsn1_serde::macro_alias::ContentsRef };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };
    let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

    let Result = quote! { ::std::result::Result };
    let From = quote! { ::std::convert::From };

    Ok(quote! {
        unsafe fn from_ber(id: &#IdRef, length: #Length, contents: &#ContentsRef)
            -> #Result<Self, #Error> {
            let val: #ty = #Deserialize::from_ber(id, length, contents)?;
            #Result::Ok(#From::from(val))
        }

        fn from_der(id: &#IdRef, contents: &#ContentsRef) -> #Result<Self, #Error> {
            let val: #ty = #Deserialize::from_der(id, contents)?;
            #Result::Ok(#From::from(val))
        }
    })
}

#[allow(non_snake_case)]
fn do_try_from_deserialize(ty: &syn::Path) -> syn::Result<TokenStream> {
    let IdRef = quote! { ::bsn1_serde::macro_alias::IdRef };
    let Length = quote! { ::bsn1_serde::macro_alias::Length };
    let ContentsRef = quote! { ::bsn1_serde::macro_alias::ContentsRef };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };
    let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

    let Result = quote! { ::std::result::Result };
    let TryFrom = quote! { ::std::convert::TryFrom };
    let Anyhow = quote! { ::anyhow::Error };

    Ok(quote! {
        unsafe fn from_ber(id: &#IdRef, length: #Length, contents: &#ContentsRef)
            -> #Result<Self, #Error> {
            let val: #ty = #Deserialize::from_ber(id, length, contents)?;
            #TryFrom::try_from(val).map_err(|err| {
                let err = #Anyhow::new(err);
                #Error::from(err)
            })
        }

        fn from_der(id: &#IdRef, contents: &#ContentsRef) -> #Result<Self, #Error> {
            let val: #ty = #Deserialize::from_der(id, contents)?;
            #TryFrom::try_from(val).map_err(|err| {
                let err = #Anyhow::new(err);
                #Error::from(err)
            })
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
    let length = quote! { length };
    let contents = quote! { contents };

    let (from_ber, from_der) = if data.attribute().is_transparent() {
        let from_ber = data.from_ber_transparent(&id, &length, &contents)?;
        let from_der = data.from_der_transparent(&id, &contents)?;

        (from_ber, from_der)
    } else {
        let id_slice = data.id_slice()?;
        let from_ber = data.from_ber_contents(&length, &contents)?;
        let from_der = data.from_der_contents(&contents)?;

        (
            quote! {
                if #id.as_ref() as &[u8] != #id_slice {
                    return #Result::Err(#Error::UnmatchedId);
                }
                #from_ber
            },
            quote! {
                if #id.as_ref() as &[u8] != #id_slice {
                    return #Result::Err(#Error::UnmatchedId);
                }
                #from_der
            },
        )
    };

    Ok(quote! {
        unsafe fn from_ber(id: &#IdRef, length: #Length, contents: &#ContentsRef)
            -> #Result<Self, #Error> {
            #from_ber
        }

        fn from_der(id: &#IdRef, contents: &#ContentsRef) -> #Result<Self, #Error> {
            #from_der
        }
    })
}

#[allow(non_snake_case)]
fn do_deserialize_enum(
    attribute: Attribute,
    enum_name: &Ident,
    data: syn::DataEnum,
) -> syn::Result<TokenStream> {
    attribute.sanitize_as_enum()?;

    let IdRef = quote! { ::bsn1_serde::macro_alias::IdRef };
    let Length = quote! { ::bsn1_serde::macro_alias::Length };
    let ContentsRef = quote! { ::bsn1_serde::macro_alias::ContentsRef };
    let Error = quote! { ::bsn1_serde::macro_alias::Error };

    let Result = quote! { ::std::result::Result };

    let length = quote! { length };
    let contents = quote! { contents };
    let mut variants = Vec::new();
    let mut from_bers = Vec::new();
    let mut from_ders = Vec::new();
    let mut arm_id_slices = Vec::new();

    for variant in data.variants.into_iter() {
        let variant = DataContainer::try_from((enum_name.clone(), variant))?;
        let id_slice = variant.id_slice()?;
        let from_ber = variant.from_ber_contents(&length, &contents)?;
        let from_der = variant.from_der_contents(&contents)?;

        variants.push(variant);
        from_bers.push(from_ber);
        from_ders.push(from_der);
        arm_id_slices.push(id_slice);
    }

    Ok(quote! {
        unsafe fn from_ber(id: &#IdRef, length: #Length, contents: &#ContentsRef)
            -> #Result<Self, #Error> {
            #(if id.as_ref() as &[u8] == #arm_id_slices {
                #from_bers
            } else)* {
                #Result::Err(#Error::UnmatchedId)
            }
        }

        fn from_der(id: &#IdRef, contents: &#ContentsRef) -> #Result<Self, #Error> {
            #(if id.as_ref() as &[u8] == #arm_id_slices {
                #from_ders
            } else)* {
                #Result::Err(#Error::UnmatchedId)
            }
        }
    })
}
