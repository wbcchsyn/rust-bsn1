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

//! Provides enum `DataContainer`

use crate::Attribute;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, ToTokens};

pub enum DataContainer {
    DataStruct {
        attribute: Attribute,
        field_attributes: Vec<Attribute>,
        data_structure: syn::DataStruct,
    },
    Variant {
        enum_name: Ident,
        attribute: Attribute,
        field_attributes: Vec<Attribute>,
        variant: syn::Variant,
    },
}

impl TryFrom<(Attribute, syn::DataStruct)> for DataContainer {
    type Error = syn::Error;

    fn try_from((attribute, data): (Attribute, syn::DataStruct)) -> Result<Self, Self::Error> {
        attribute.sanitize_as_struct()?;

        let mut field_attributes = Vec::new();
        for field in data.fields.iter() {
            let attribute = Attribute::try_from(&field.attrs[..])?;
            attribute.sanitize_as_field()?;
            field_attributes.push(attribute);
        }

        Ok(Self::DataStruct {
            attribute,
            field_attributes,
            data_structure: data,
        })
    }
}

impl TryFrom<(Ident, syn::Variant)> for DataContainer {
    type Error = syn::Error;

    fn try_from((enum_name, value): (Ident, syn::Variant)) -> Result<Self, Self::Error> {
        let attribute = Attribute::try_from(&value.attrs[..])?;
        attribute.sanitize_as_variant()?;

        let mut field_attributes = Vec::new();
        for field in value.fields.iter() {
            let attribute = Attribute::try_from(&field.attrs[..])?;
            attribute.sanitize_as_field()?;
            field_attributes.push(attribute);
        }

        Ok(Self::Variant {
            enum_name,
            attribute,
            field_attributes,
            variant: value,
        })
    }
}

impl DataContainer {
    /// # Safety
    ///
    /// This method supports only `DataContainer::Variant`.
    pub unsafe fn to_match_arm(&self) -> syn::Result<TokenStream> {
        match self {
            Self::Variant { .. } => {
                let ident = self.ident();
                let fields = self.field_idents();
                let vars = self.field_vars();

                match self.fields() {
                    syn::Fields::Named(_) => Ok(quote! { Self::#ident { #(#fields: #vars,)* } }),
                    syn::Fields::Unnamed(_) => Ok(quote! { Self::#ident ( #(#vars,)* ) }),
                    syn::Fields::Unit => Ok(quote! { Self::#ident }),
                }
            }
            Self::DataStruct { .. } => {
                panic!("This method supports only `DataContainer::Variant`.")
            }
        }
    }

    #[allow(non_snake_case)]
    pub fn write_id(&self, buffer: &TokenStream) -> syn::Result<TokenStream> {
        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Write = quote! { ::std::io::Write };

        let id = self.id_slice()?;
        Ok(quote! { #Write::write_all(#buffer, &#id).map_err(#Error::from) })
    }

    #[allow(non_snake_case)]
    pub fn id_len(&self) -> syn::Result<TokenStream> {
        let Result = quote! { ::std::result::Result };

        let id = self.id_slice()?;
        Ok(quote! { #Result::Ok(#id.len()) })
    }

    pub fn id_slice(&self) -> syn::Result<TokenStream> {
        // This method should not be called if converting annottation is specified.
        assert!(self.attribute().into_type().is_none());
        assert!(self.attribute().from_type().is_none());
        assert!(self.attribute().to_path().is_none());
        assert!(self.attribute().try_from_type().is_none());

        const SEQUENCE: u8 = 0x30;

        match self.attribute().id(SEQUENCE) {
            Some(id) => Ok(id),
            None => Ok(quote! { [#SEQUENCE] }),
        }
    }

    #[allow(non_snake_case)]
    pub fn write_der_contents(&self, buffer: &TokenStream) -> syn::Result<TokenStream> {
        let Length = quote! { ::bsn1_serde::macro_alias::Length };
        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Serialize = quote! { ::bsn1_serde::ser::Serialize };
        let Result = quote! { ::std::result::Result };
        let Write = quote! { ::std::io::Write };

        let contents_len = quote! { bsn1_macro_1704044765_contents_len };
        let length = quote! { bsn1_macro_1704044765_length };

        let field_write = self
            .field_vars()
            .into_iter()
            .zip(self.field_attributes())
            .map(|(field, attribute)| {
                if attribute.is_skip_serializing() {
                    quote! {}
                } else if let Some(into_ty) = attribute.into_type() {
                    let Clone = quote! { ::std::clone::Clone };
                    let Into = quote! { ::std::convert::Into };
                    let this = quote! { bsn1_macro_1704044765_this };

                    quote! {{
                        let #this = #Clone::clone(#field);
                        let #this: #into_ty = #Into::into(#this);
                        #Serialize::write_id(&#this, buffer)?;

                        let #contents_len = #Serialize::der_contents_len(&#this)?;
                        let #length = #Length::Definite(#contents_len).to_bytes();
                        #Write::write_all(#buffer, &#length).map_err(#Error::from)?;
                        #Serialize::write_der_contents(&#this, buffer)?;
                    }}
                } else if let Some(to_path) = attribute.to_path() {
                    let this = quote! { bsn1_macro_1705721776_this };

                    quote! {{
                        let #this = #to_path(#field);
                        #Serialize::write_id(&#this, buffer)?;

                        let #contents_len = #Serialize::der_contents_len(&#this)?;
                        let #length = #Length::Definite(#contents_len).to_bytes();
                        #Write::write_all(#buffer, &#length).map_err(#Error::from)?;
                        #Serialize::write_der_contents(&#this, buffer)?;
                    }}
                } else {
                    quote! {{
                        #Serialize::write_id(#field, buffer)?;
                        let #contents_len = #Serialize::der_contents_len(#field)?;
                        let #length = #Length::Definite(#contents_len).to_bytes();
                        #Write::write_all(#buffer, &#length).map_err(#Error::from)?;
                        #Serialize::write_der_contents(#field, buffer)?;
                    }}
                }
            });

        Ok(quote! {{
                #(#field_write)*
                #Result::Ok(())
        }})
    }

    #[allow(non_snake_case)]
    pub fn der_contents_len(&self) -> syn::Result<TokenStream> {
        let Length = quote! { ::bsn1_serde::macro_alias::Length };
        let Result = quote! { ::std::result::Result };
        let Serialize = quote! { ::bsn1_serde::ser::Serialize };

        let ret = quote! { bsn1_macro_1704043457_ret };
        let contents_len = quote! { bsn1_macro_1704043457_contents_len };
        let length_len = quote! { bsn1_macro_1704043457_length_len};

        let field_acc = self
            .field_vars()
            .into_iter()
            .zip(self.field_attributes())
            .map(|(field, attribute)| {
                if attribute.is_skip_serializing() {
                    quote! {}
                } else if let Some(into_ty) = attribute.into_type() {
                    let Clone = quote! { ::std::clone::Clone };
                    let Into = quote! { ::std::convert::Into };
                    let this = quote! { bsn1_macro_1704043457_this };

                    quote! {{
                        let #this = #Clone::clone(#field);
                        let #this: #into_ty = #Into::into(#this);
                        let #contents_len = #Serialize::der_contents_len(&#this)?;
                        let #length_len = #Length::Definite(#contents_len).len();
                        #ret += #Serialize::id_len(&#this)? + #length_len + #contents_len;
                    }}
                } else if let Some(to_path) = attribute.to_path() {
                    let this = quote! { bsn1_macro_1705721776_this };

                    quote! {{
                        let #this = #to_path(#field);
                        let #contents_len = #Serialize::der_contents_len(&#this)?;
                        let #length_len = #Length::Definite(#contents_len).len();
                        #ret += #Serialize::id_len(&#this)? + #length_len + #contents_len;
                    }}
                } else {
                    quote! {{
                        let #contents_len = #Serialize::der_contents_len(#field)?;
                        let #length_len = #Length::Definite(#contents_len).len();
                        #ret += #Serialize::id_len(#field)? + #length_len + #contents_len;
                    }}
                }
            });

        Ok(quote! {
            let mut #ret = 0;
            #(#field_acc)*
            #Result::Ok(#ret)
        })
    }

    #[allow(non_snake_case)]
    pub fn from_ber_contents(
        &self,
        length: &TokenStream,
        contents: &TokenStream,
    ) -> syn::Result<TokenStream> {
        let BerRef = quote! { ::bsn1_serde::macro_alias::BerRef };
        let Length = quote! { ::bsn1_serde::macro_alias::Length };
        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

        let Result = quote! { ::std::result::Result };

        let contents_bytes = quote! { bsn1_macro_1704080283_contents_bytes };
        let contents_length = quote! { bsn1_macro_1704080283_length };
        let eoc = quote! { bsn1_macro_1704080283_eoc };
        let tmp_ber = quote! { bsn1_macro_1704080283_tmp_ber };
        let ret = quote! { bsn1_macro_1704080283_ret };
        let ty = self.ty();

        let field_constructors = self.field_attributes().iter().map(|attribute| {
            if attribute.is_skip_deserializing() {
                let path = attribute.default_path();
                quote! { #path() }
            } else if let Some(from_ty) = attribute.from_type() {
                let From = quote! { ::std::convert::From };
                let tmp_val = quote! { bsn1_macro_1704080283_tmp_val };
                quote! {{
                    let #tmp_ber = #BerRef::parse(#contents_bytes)?;
                    let #tmp_val: #from_ty = #Deserialize::from_ber(
                                                #tmp_ber.id(),
                                                #tmp_ber.length(),
                                                #tmp_ber.contents())?;
                    #From::from(#tmp_val)
                }}
            } else if let Some(try_from_ty) = attribute.try_from_type() {
                let TryFrom = quote! { ::std::convert::TryFrom };
                let tmp_val = quote! { bsn1_macro_1705741001_tmp_val };
                quote! {{
                    let #tmp_ber = #BerRef::parse(#contents_bytes)?;
                    let #tmp_val: #try_from_ty = #Deserialize::from_ber(
                                                #tmp_ber.id(),
                                                #tmp_ber.length(),
                                                #tmp_ber.contents())?;
                    #TryFrom::try_from(#tmp_val).map_err(|err| #Error::from(Box::new(err)))?
                }}
            } else {
                quote! {{
                    let #tmp_ber = #BerRef::parse(#contents_bytes)?;
                    #Deserialize::from_ber(#tmp_ber.id(), #tmp_ber.length(), #tmp_ber.contents())?
                }}
            }
        });

        let constructor = match self.fields() {
            syn::Fields::Named(_) => {
                let fields = self.field_idents();
                quote! { #ty { #(#fields: #field_constructors,)* } }
            }
            syn::Fields::Unnamed(_) => quote! { #ty ( #(#field_constructors,)* ) },
            syn::Fields::Unit => quote! { #ty },
        };

        Ok(quote! {{
            let mut #contents_bytes: &[u8] = match #length {
                #Length::Definite(#contents_length) => {
                    debug_assert_eq!(#contents_length, #contents.len());
                    #contents.as_ref()
                }
                #Length::Indefinite => {
                    let #contents_bytes: &[u8] = #contents.as_ref();
                    let #eoc: &[u8] = #BerRef::eoc().as_ref();
                    if #contents_bytes.ends_with(#eoc) {
                        &#contents_bytes[..(#contents_bytes.len() - #eoc.len())]
                    } else {
                        return #Result::Err(#Error::UnTerminatedBytes);
                    }
                }
            };
            let #contents_bytes = &mut #contents_bytes;
            let #ret = #constructor;

            if #contents_bytes.len() == 0 {
                #Result::Ok(#ret)
            } else {
                return #Result::Err(#Error::InvalidContents);
            }
        }})
    }

    #[allow(non_snake_case)]
    pub fn from_der_contents(&self, contents: &TokenStream) -> syn::Result<TokenStream> {
        let DerRef = quote! { ::bsn1_serde::macro_alias::DerRef };
        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

        let Result = quote! { ::std::result::Result };

        let contents_bytes = quote! { bsn1_macro_1704080283_contents_bytes };
        let tmp_der = quote! { bsn1_macro_1704080283_tmp_der };
        let ret = quote! { bsn1_macro_1704080283_ret };
        let ty = self.ty();

        let field_constructors = self.field_attributes().iter().map(|attribute| {
            if attribute.is_skip_deserializing() {
                let path = attribute.default_path();
                quote! { #path() }
            } else if let Some(from_ty) = attribute.from_type() {
                let From = quote! { ::std::convert::From };
                let tmp_val = quote! { bsn1_macro_1704080283_tmp_val };
                quote! {{
                    let #tmp_der = #DerRef::parse(#contents_bytes)?;
                    let #tmp_val: #from_ty = #Deserialize::from_der(
                                                #tmp_der.id(),
                                                #tmp_der.contents())?;
                    #From::from(#tmp_val)
                }}
            } else if let Some(try_from_ty) = attribute.try_from_type() {
                let TryFrom = quote! { ::std::convert::TryFrom };
                let tmp_val = quote! { bsn1_macro_1705741001_tmp_val };
                quote! {{
                    let #tmp_der = #DerRef::parse(#contents_bytes)?;
                    let #tmp_val: #try_from_ty = #Deserialize::from_der(
                                                #tmp_der.id(),
                                                #tmp_der.contents())?;
                    #TryFrom::try_from(#tmp_val).map_err(|err| #Error::from(Box::new(err)))?
                }}
            } else {
                quote! {{
                    let #tmp_der = #DerRef::parse(#contents_bytes)?;
                    #Deserialize::from_der(#tmp_der.id(), #tmp_der.contents())?
                }}
            }
        });

        let constructor = match self.fields() {
            syn::Fields::Named(_) => {
                let fields = self.field_idents();
                quote! { #ty { #(#fields: #field_constructors,)* } }
            }
            syn::Fields::Unnamed(_) => quote! { #ty ( #(#field_constructors,)* ) },
            syn::Fields::Unit => quote! { #ty },
        };

        Ok(quote! {{
            let mut #contents_bytes: &[u8] = #contents.as_ref();
            let #contents_bytes = &mut #contents_bytes;
            let #ret = #constructor;

            if #contents_bytes.len() == 0 {
                #Result::Ok(#ret)
            } else {
                return #Result::Err(#Error::InvalidContents);
            }
        }})
    }

    fn attribute(&self) -> &Attribute {
        match self {
            Self::DataStruct { attribute, .. } => attribute,
            Self::Variant { attribute, .. } => attribute,
        }
    }

    fn ty(&self) -> TokenStream {
        match self {
            Self::DataStruct { .. } => quote! { Self },
            Self::Variant {
                enum_name, variant, ..
            } => {
                let variant_name = &variant.ident;
                quote! { #enum_name::#variant_name }
            }
        }
    }

    fn ident(&self) -> TokenStream {
        match self {
            Self::DataStruct { .. } => quote! { Self },
            Self::Variant { variant, .. } => variant.ident.to_token_stream(),
        }
    }

    fn fields(&self) -> &syn::Fields {
        match self {
            Self::Variant { variant, .. } => &variant.fields,
            Self::DataStruct { data_structure, .. } => &data_structure.fields,
        }
    }

    fn field_idents(&self) -> Vec<TokenStream> {
        match self.fields() {
            syn::Fields::Named(fields) => fields
                .named
                .iter()
                .map(|field| field.ident.as_ref().unwrap().to_token_stream())
                .collect(),
            syn::Fields::Unnamed(fields) => (0..fields.unnamed.len())
                .map(|i| syn::Index::from(i).to_token_stream())
                .collect(),
            syn::Fields::Unit => Vec::new(),
        }
    }

    fn field_vars(&self) -> Vec<TokenStream> {
        match self {
            Self::Variant { .. } => {
                static PREFIX: &str = "bsn1_macro_field_1701146321";
                self.field_idents()
                    .into_iter()
                    .map(|ident| {
                        format_ident!("{}_{}", PREFIX, ident.to_string()).to_token_stream()
                    })
                    .collect()
            }
            Self::DataStruct { .. } => self
                .field_idents()
                .into_iter()
                .map(|ident| quote! { &self.#ident })
                .collect(),
        }
    }

    fn field_attributes(&self) -> &[Attribute] {
        match self {
            Self::Variant {
                field_attributes, ..
            } => field_attributes,
            Self::DataStruct {
                field_attributes, ..
            } => field_attributes,
        }
    }
}
