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

#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

mod attribute;
mod data_container;
mod de;
mod ser;

use attribute::Attribute;
use data_container::DataContainer;
use proc_macro::TokenStream;

/// Derive macro to implement `ser::Serialize` trait for struct or enum.
///
/// User can customize the implementation by attributes `bsn1_serde`.
///
/// All the fields of the struct or enum must implement `ser::Serialize`
/// unless the field is annotated with `#[bsn1_serde(to = "...")]` or `#[bsn1_serde(into = "...")]`
#[doc = include_str!("../annotation_bsn1_serde.md")]
#[proc_macro_derive(Serialize, attributes(bsn1_serde))]
pub fn serialize(input: TokenStream) -> TokenStream {
    let ast = syn::parse_macro_input!(input as syn::DeriveInput);

    match ser::do_serialize(ast) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Derive macro to implement `de::Deserialize` trait for struct or enum.
///
/// User can customize the implementation by attributes `bsn1_serde`.
///
/// All the fields of the struct or enum must implement `de::Deserialize`
/// unless the field is annotated with `#[bsn1_serde(from = "...")]` or
/// `#[bsn1_serde(try_from = "...")]`
#[doc = include_str!("../annotation_bsn1_serde.md")]
#[proc_macro_derive(Deserialize, attributes(bsn1_serde))]
pub fn deserialize(input: TokenStream) -> TokenStream {
    let ast = syn::parse_macro_input!(input as syn::DeriveInput);

    match de::do_deserialize(ast) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}
