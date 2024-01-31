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
}
