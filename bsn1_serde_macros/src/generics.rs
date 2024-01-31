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

use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

pub struct Generics(syn::Generics);

impl From<syn::Generics> for Generics {
    fn from(generics: syn::Generics) -> Self {
        Self(generics)
    }
}

impl Generics {
    pub fn ident_bounds(&self) -> TokenStream {
        if self.0.params.is_empty() {
            quote! {}
        } else {
            let it = self.0.params.iter().map(|param| match param {
                syn::GenericParam::Lifetime(lifetime) => lifetime.to_token_stream(),
                syn::GenericParam::Type(ty) => {
                    let ident = &ty.ident;
                    let colon = &ty.colon_token;
                    let bounds = &ty.bounds;
                    quote! { #ident #colon #bounds }
                }
                syn::GenericParam::Const(constant) => {
                    let ident = &constant.ident;
                    let ty = &constant.ty;
                    quote! { const #ident : #ty }
                }
            });
            quote! { <#(#it,)*> }
        }
    }

    pub fn idents(&self) -> TokenStream {
        if self.0.params.is_empty() {
            quote! {}
        } else {
            let it = self.0.params.iter().map(|param| match param {
                syn::GenericParam::Lifetime(lifetime) => lifetime.lifetime.to_token_stream(),
                syn::GenericParam::Type(ty) => ty.ident.to_token_stream(),
                syn::GenericParam::Const(constant) => constant.ident.to_token_stream(),
            });
            quote! { <#(#it,)*> }
        }
    }

    pub fn where_clause(&self) -> Option<&syn::WhereClause> {
        self.0.where_clause.as_ref()
    }
}
