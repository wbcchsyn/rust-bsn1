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

//! Provides enum `DataContainer`

use crate::Attribute;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, ToTokens};

pub enum DataContainer {
    DataStruct {
        struct_name: Ident,
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

impl TryFrom<(Attribute, Ident, syn::DataStruct)> for DataContainer {
    type Error = syn::Error;

    fn try_from(
        (attribute, struct_name, data): (Attribute, Ident, syn::DataStruct),
    ) -> Result<Self, Self::Error> {
        attribute.sanitize_as_struct()?;

        let mut field_attributes = Vec::new();
        for field in data.fields.iter() {
            let attribute = Attribute::try_from(&field.attrs[..])?;
            attribute.sanitize_as_field()?;
            field_attributes.push(attribute);
        }

        Ok(Self::DataStruct {
            struct_name,
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
            Self::Variant { variant, .. } => {
                let ident = variant.ident.to_token_stream();
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
    pub fn write_id_transparent(&self, buffer: &TokenStream) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Serialize = quote! { ::bsn1_serde::ser::Serialize };
        let field = self.transparent_field_var(true)?;
        let field_attribute = self.transparent_field_attribute(true)?;

        if let Some(into_ty) = field_attribute.into_type() {
            let Clone = quote! { ::std::clone::Clone };
            let Into = quote! { ::std::convert::Into };
            let this = quote! { bsn1_macro_1704044765_this };

            Ok(quote! {{
                let #this = #Clone::clone(#field);
                let #this: #into_ty = #Into::into(#this);
                #Serialize::write_id(&#this, #buffer)
            }})
        } else if let Some(path) = field_attribute.to_path() {
            let this = quote! { bsn1_macro_1706411411_this };

            Ok(quote! {{
                let #this = #path(#field);
                #Serialize::write_id(&#this, #buffer)
            }})
        } else {
            Ok(quote! { #Serialize::write_id(#field, #buffer) })
        }
    }

    #[allow(non_snake_case)]
    pub fn id_len(&self) -> syn::Result<TokenStream> {
        let Result = quote! { ::std::result::Result };
        let Option = quote! { ::std::option::Option };

        let id = self.id_slice()?;
        Ok(quote! { #Result::Ok(#Option::Some(#id.len())) })
    }

    #[allow(non_snake_case)]
    pub fn id_len_transparent(&self) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Result = quote! { ::std::result::Result };
        let Option = quote! { ::std::option::Option };
        let Serialize = quote! { ::bsn1_serde::ser::Serialize };
        let field = self.transparent_field_var(true)?;
        let field_attribute = self.transparent_field_attribute(true)?;

        if field_attribute.into_type().is_some() || field_attribute.to_path().is_some() {
            Ok(quote! { #Result::Ok(#Option::None) })
        } else {
            Ok(quote! { #Serialize::id_len(#field) })
        }
    }

    pub fn id_slice(&self) -> syn::Result<TokenStream> {
        const SEQUENCE: u8 = 0x30;

        match self.attribute().id(SEQUENCE) {
            Some(id) => Ok(id),
            None => Ok(quote! { [#SEQUENCE] }),
        }
    }

    #[allow(non_snake_case)]
    pub fn write_der_contents(&self, buffer: &TokenStream) -> syn::Result<TokenStream> {
        let field_ref = quote! { bsn1_macro_1711342495_field_ref };

        let field_builders = self
            .field_vars()
            .into_iter()
            .zip(self.field_attributes())
            .map(|(field, attr)| {
                if attr.is_skip_serializing() {
                    quote! {}
                } else if let Some(into_ty) = attr.into_type() {
                    let Clone = quote! { ::std::clone::Clone };
                    let Into = quote! { ::std::convert::Into };
                    quote! {
                        let #field_ref: #into_ty = #Into::into(#Clone::clone(#field));
                        let #field_ref = &#field_ref;
                    }
                } else if let Some(to_path) = attr.to_path() {
                    quote! {
                        let #field_ref = #to_path(#field);
                        let #field_ref = &#field_ref;
                    }
                } else {
                    quote! { let #field_ref = #field; }
                }
            });

        let Result = quote! { ::std::result::Result };
        let crate_bsn1_serde = quote! { ::bsn1_serde };

        let write_fields =
            field_builders
                .zip(self.field_attributes())
                .map(|(field_builder, attr)| {
                    if attr.is_skip_serializing() {
                        quote! {}
                    } else {
                        quote! {{
                            #field_builder
                            #crate_bsn1_serde::write_der(#field_ref, #buffer)?;
                        }}
                    }
                });

        Ok(quote! {{
            #(#write_fields)*
            #Result::Ok(())
        }})
    }

    #[allow(non_snake_case)]
    pub fn write_der_contents_transparent(&self, buffer: &TokenStream) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Serialize = quote! { ::bsn1_serde::ser::Serialize };
        let field = self.transparent_field_var(true)?;
        let field_attribute = self.transparent_field_attribute(true)?;

        if let Some(into_ty) = field_attribute.into_type() {
            let Clone = quote! { ::std::clone::Clone };
            let Into = quote! { ::std::convert::Into };
            let this = quote! { bsn1_macro_1704044765_this };

            Ok(quote! {{
                let #this = #Clone::clone(#field);
                let #this: #into_ty = #Into::into(#this);
                #Serialize::write_der_contents(&#this, #buffer)
            }})
        } else if let Some(to_path) = field_attribute.to_path() {
            let this = quote! { bsn1_macro_1705721776_this };

            Ok(quote! {{
                let #this = #to_path(#field);
                #Serialize::write_der_contents(&#this, #buffer)
            }})
        } else {
            Ok(quote! { #Serialize::write_der_contents(#field, #buffer) })
        }
    }

    #[allow(non_snake_case)]
    pub fn der_contents_len(&self) -> syn::Result<TokenStream> {
        let Result = quote! { ::std::result::Result };
        let Option = quote! { ::std::option::Option };

        // If any field is annotated as `into`, or `to`, return `None` immediately.
        if self
            .field_attributes()
            .iter()
            .any(|attr| attr.into_type().is_some() || attr.to_path().is_some())
        {
            return Ok(quote! { #Result::Ok(#Option::None) });
        }

        let Length = quote! { ::bsn1_serde::macro_alias::Length };
        let Serialize = quote! { ::bsn1_serde::ser::Serialize };

        let ret = quote! { bsn1_macro_1704043457_ret };
        let id_len = quote! { bsn1_macro_1711551123_contents_len };
        let contents_len = quote! { bsn1_macro_1704043457_contents_len };
        let length_len = quote! { bsn1_macro_1704043457_length_len};

        let field_acc = self
            .field_vars()
            .into_iter()
            .zip(self.field_attributes())
            .map(|(field, attribute)| {
                assert!(attribute.into_type().is_none());
                assert!(attribute.to_path().is_none());

                if attribute.is_skip_serializing() {
                    quote! {}
                } else {
                    quote! {{
                        if let Some(#contents_len) = #Serialize::der_contents_len(#field)? {
                            if let Some(#id_len) = #Serialize::id_len(#field)? {
                                let #length_len = #Length::Definite(#contents_len).len();
                                #ret += #id_len + #length_len + #contents_len;
                            } else {
                                return #Result::Ok(#Option::None);
                            }
                        } else {
                            return #Result::Ok(#Option::None);
                        }
                    }}
                }
            });

        Ok(quote! {{
            let mut #ret = 0;
            #(#field_acc)*
            #Result::Ok(#Option::Some(#ret))
        }})
    }

    #[allow(non_snake_case)]
    pub fn der_contents_len_transparent(&self) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let field_attribute = self.transparent_field_attribute(true)?;

        if field_attribute.into_type().is_some() || field_attribute.to_path().is_some() {
            let Result = quote! { ::std::result::Result };
            let Option = quote! { ::std::option::Option };
            Ok(quote! { #Result::Ok(#Option::None) })
        } else {
            let Serialize = quote! { ::bsn1_serde::ser::Serialize };
            let field = self.transparent_field_var(true)?;
            Ok(quote! { #Serialize::der_contents_len(#field) })
        }
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

        let Anyhow = quote! { ::anyhow::Error };
        let Result = quote! { ::std::result::Result };

        let ty = self.ty();
        let contents_bytes = quote! { bsn1_macro_1704080283_contents_bytes };

        let field_constructors = self.field_attributes().iter().zip(self.field_idents()).map(
            |(attribute, field_ident)| {
                let field_ident = quote! { #ty.#field_ident };

                let tmp_ber = quote! { bsn1_macro_1704080283_tmp_ber };
                let tmp_id = quote! { bsn1_macro_1704080283_tmp_id };
                let tmp_length = quote! { bsn1_macro_1704080283_tmp_length };
                let tmp_contents = quote! { bsn1_macro_1704080283_tmp_contents };
                let tmp_val = quote! {{
                    let #tmp_ber = #BerRef::parse(#contents_bytes).map_err(|err| {
                        let context = concat!(
                            "Failed to parse BER for `",
                            stringify!(#field_ident),
                            "`"
                        );
                        err.context(context)
                    })?;
                    let (#tmp_id, #tmp_length, #tmp_contents) = #tmp_ber.disassemble();
                    #Deserialize::from_ber(#tmp_id, #tmp_length, #tmp_contents).map_err(|err| {
                        let context = concat!(
                            "Failed to deserialize BER into `",
                            stringify!(#field_ident),
                            "`"
                        );
                        err.context(context)
                    })?
                }};

                if attribute.is_skip_deserializing() {
                    let path = attribute.default_path();
                    quote! { #path() }
                } else if let Some(from_ty) = attribute.from_type() {
                    let From = quote! { ::std::convert::From };
                    quote! { #From::<#from_ty>::from(#tmp_val) }
                } else if let Some(try_from_ty) = attribute.try_from_type() {
                    let TryFrom = quote! { ::std::convert::TryFrom };
                    quote! {
                        #TryFrom::<#try_from_ty>::try_from(#tmp_val).map_err(|err| {
                            let context = concat!(
                                "Failed to convert `",
                                stringify!(#try_from_ty),
                                "` into `",
                                stringify!(#field_ident),
                                "`"
                            );
                            #Error::from(#Anyhow::new(err)).context(context)
                        })?
                    }
                } else {
                    tmp_val
                }
            },
        );

        let constructor = match self.fields() {
            syn::Fields::Named(_) => {
                let fields = self.field_idents();
                quote! { #ty { #(#fields: #field_constructors,)* } }
            }
            syn::Fields::Unnamed(_) => quote! { #ty ( #(#field_constructors,)* ) },
            syn::Fields::Unit => quote! { #ty },
        };

        let ret = quote! { bsn1_macro_1704080283_ret };
        let eoc = quote! { bsn1_macro_1704080283_eoc };
        let contents_length = quote! { bsn1_macro_1704080283_length };

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
                        return #Result::Err(#Error::UnterminatedBytes);
                    }
                }
            };
            let #contents_bytes = &mut #contents_bytes;
            let #ret = #constructor;

            if #contents_bytes.len() == 0 {
                #Result::Ok(#ret)
            } else {
                return #Result::Err(#Error::ExtraContentsOctet);
            }
        }})
    }

    #[allow(non_snake_case)]
    pub fn from_ber_transparent(
        &self,
        id: &TokenStream,
        length: &TokenStream,
        contents: &TokenStream,
    ) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

        let Result = quote! { ::std::result::Result };
        let Anyhow = quote! { ::anyhow::Error };

        let ty = self.ty();
        let field_idents = self.field_idents();
        let mut deserialized_fields: usize = 0;

        let field_constructors =
            self.field_attributes()
                .iter()
                .zip(&field_idents)
                .map(|(attribute, field_ident)| {
                    let field_ident = quote! { #ty.#field_ident };
                    let tmp_val =
                        quote! { #Deserialize::from_ber(#id, #length, #contents).map_err(|err| {
                            let context = concat!(
                                "Failed to deserialize BER into `",
                                stringify!(#field_ident),
                                "`"
                            );
                            err.context(context)
                        })? };

                    if attribute.is_skip_deserializing() {
                        let path = attribute.default_path();
                        quote! { #path() }
                    } else if let Some(from_ty) = attribute.from_type() {
                        deserialized_fields += 1;
                        let From = quote! { ::std::convert::From };
                        quote! { #From::<#from_ty>::from(#tmp_val) }
                    } else if let Some(try_from_ty) = attribute.try_from_type() {
                        deserialized_fields += 1;
                        let TryFrom = quote! { ::std::convert::TryFrom };
                        quote! {
                            #TryFrom::<#try_from_ty>::try_from(#tmp_val).map_err(|err| {
                                let context = concat!(
                                    "Failed to convert `",
                                    stringify!(#try_from_ty),
                                    "` into `",
                                    stringify!(#field_ident),
                                    "`"
                                );
                                #Error::from(#Anyhow::new(err)).context(context)
                            })?
                        }
                    } else {
                        deserialized_fields += 1;
                        tmp_val
                    }
                });

        let ret = match self.fields() {
            syn::Fields::Named(_) => {
                quote! { #ty { #(#field_idents: #field_constructors,)* } }
            }
            syn::Fields::Unnamed(_) => quote! { #ty ( #(#field_constructors,)* ) },
            syn::Fields::Unit => quote! { #ty },
        };

        if deserialized_fields != 1 {
            return Err(syn::Error::new_spanned(
                self.attribute().transparent_token(),
                "Transparent struct must have exactly one field to be deserialized.",
            ));
        }

        Ok(quote! { #Result::Ok(#ret) })
    }

    #[allow(non_snake_case)]
    pub fn from_der_contents(&self, contents: &TokenStream) -> syn::Result<TokenStream> {
        let DerRef = quote! { ::bsn1_serde::macro_alias::DerRef };
        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

        let Result = quote! { ::std::result::Result };
        let Anyhow = quote! { ::anyhow::Error };

        let ty = self.ty();
        let contents_bytes = quote! { bsn1_macro_1704080283_contents_bytes };

        let field_constructors = self.field_attributes().iter().zip(self.field_idents()).map(
            |(attribute, field_ident)| {
                let field_ident = quote! { #ty.#field_ident };

                let tmp_der = quote! { bsn1_macro_1704080283_tmp_der };
                let tmp_id = quote! { bsn1_macro_1704080283_tmp_id };
                let tmp_contents = quote! { bsn1_macro_1704080283_tmp_contents };
                let tmp_val = quote! {{
                    let #tmp_der = #DerRef::parse(#contents_bytes).map_err(|err| {
                        let context = concat!(
                            "Failed to parse DER for `",
                            stringify!(#field_ident),
                            "`"
                        );
                        err.context(context)
                    })?;
                    let (#tmp_id, _, #tmp_contents) = #tmp_der.disassemble();
                    #Deserialize::from_der(#tmp_id, #tmp_contents).map_err(|err| {
                        let context = concat!(
                            "Failed to deserialize DER into `",
                            stringify!(#field_ident),
                            "`");
                        err.context(context)
                    })?
                }};

                if attribute.is_skip_deserializing() {
                    let path = attribute.default_path();
                    quote! { #path() }
                } else if let Some(from_ty) = attribute.from_type() {
                    let From = quote! { ::std::convert::From };
                    quote! { #From::<#from_ty>::from(#tmp_val) }
                } else if let Some(try_from_ty) = attribute.try_from_type() {
                    let TryFrom = quote! { ::std::convert::TryFrom };
                    quote! {
                        #TryFrom::<#try_from_ty>::try_from(#tmp_val).map_err(|err| {
                            let context = concat!(
                                "Failed to convert `",
                                stringify!(#try_from_ty),
                                "` into `",
                                stringify!(#field_ident),
                                "`"
                            );
                            #Error::from(#Anyhow::new(err)).context(context)
                        })?
                    }
                } else {
                    tmp_val
                }
            },
        );

        let constructor = match self.fields() {
            syn::Fields::Named(_) => {
                let fields = self.field_idents();
                quote! { #ty { #(#fields: #field_constructors,)* } }
            }
            syn::Fields::Unnamed(_) => quote! { #ty ( #(#field_constructors,)* ) },
            syn::Fields::Unit => quote! { #ty },
        };

        let ret = quote! { bsn1_macro_1704080283_ret };

        Ok(quote! {{
            let mut #contents_bytes: &[u8] = #contents.as_ref();
            let #contents_bytes = &mut #contents_bytes;
            let #ret = #constructor;

            if #contents_bytes.len() == 0 {
                #Result::Ok(#ret)
            } else {
                return #Result::Err(#Error::ExtraContentsOctet);
            }
        }})
    }

    #[allow(non_snake_case)]
    pub fn from_der_transparent(
        &self,
        id: &TokenStream,
        contents: &TokenStream,
    ) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

        let Result = quote! { ::std::result::Result };
        let Anyhow = quote! { ::anyhow::Error };

        let ty = self.ty();
        let field_idents = self.field_idents();
        let mut deserialized_fields: usize = 0;

        let field_constructors =
            self.field_attributes()
                .iter()
                .zip(&field_idents)
                .map(|(attribute, field_ident)| {
                    let field_ident = quote! { #ty.#field_ident };
                    let tmp_val = quote! { #Deserialize::from_der(#id, #contents).map_err(|err| {
                        let context = concat!(
                            "Failed to deserialize DER into `",
                            stringify!(#field_ident),
                            "`"
                        );
                        err.context(context)
                    })? };

                    if attribute.is_skip_deserializing() {
                        let path = attribute.default_path();
                        quote! { #path() }
                    } else if let Some(from_ty) = attribute.from_type() {
                        deserialized_fields += 1;
                        let From = quote! { ::std::convert::From };
                        quote! { #From::<#from_ty>::from(#tmp_val) }
                    } else if let Some(try_from_ty) = attribute.try_from_type() {
                        deserialized_fields += 1;
                        let TryFrom = quote! { ::std::convert::TryFrom };
                        quote! {
                            #TryFrom::<#try_from_ty>::try_from(#tmp_val).map_err(|err| {
                                let context = concat!(
                                    "Failed to convert `",
                                    stringify!(#try_from_ty),
                                    "` into `",
                                    stringify!(#field_ident),
                                    "`"
                                );
                                #Error::from(#Anyhow::new(err)).context(context)
                            })?
                        }
                    } else {
                        deserialized_fields += 1;
                        tmp_val
                    }
                });

        let ret = match self.fields() {
            syn::Fields::Named(_) => {
                quote! { #ty { #(#field_idents: #field_constructors,)* } }
            }
            syn::Fields::Unnamed(_) => quote! { #ty ( #(#field_constructors,)* ) },
            syn::Fields::Unit => quote! { #ty },
        };

        if deserialized_fields != 1 {
            return Err(syn::Error::new_spanned(
                self.attribute().transparent_token(),
                "Transparent struct must have exactly one field to be deserialized.",
            ));
        }

        Ok(quote! { #Result::Ok(#ret) })
    }

    pub fn attribute(&self) -> &Attribute {
        match self {
            Self::DataStruct { attribute, .. } => attribute,
            Self::Variant { attribute, .. } => attribute,
        }
    }

    fn ty(&self) -> TokenStream {
        match self {
            Self::DataStruct { struct_name, .. } => struct_name.to_token_stream(),
            Self::Variant {
                enum_name, variant, ..
            } => {
                let variant_name = &variant.ident;
                quote! { #enum_name::#variant_name }
            }
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

    fn transparent_field_var(&self, is_serializing: bool) -> Result<TokenStream, syn::Error> {
        assert!(self.attribute().is_transparent());

        let mut it = self
            .field_vars()
            .into_iter()
            .zip(self.field_attributes())
            .filter_map(|(var, attr)| {
                if is_serializing && attr.is_skip_serializing() {
                    None
                } else if is_serializing == false && attr.is_skip_deserializing() {
                    None
                } else {
                    Some(var)
                }
            });
        let ret = it.next();

        if ret.is_some() && it.next().is_none() {
            Ok(ret.unwrap())
        } else {
            Err(syn::Error::new_spanned(
                self.attribute().transparent_token(),
                "Transparent struct must have exactly one field to be serialized/deserialized.",
            ))
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

    fn transparent_field_attribute(&self, is_serializing: bool) -> Result<&Attribute, syn::Error> {
        assert!(self.attribute().is_transparent());

        let mut it = self.field_attributes().iter().filter(|attr| {
            if is_serializing && attr.is_skip_serializing() {
                false
            } else if is_serializing == false && attr.is_skip_deserializing() {
                false
            } else {
                true
            }
        });
        let ret = it.next();

        if ret.is_some() && it.next().is_none() {
            Ok(ret.unwrap())
        } else {
            Err(syn::Error::new_spanned(
                self.attribute().transparent_token(),
                "Transparent struct must have exactly one field to be serialized/deserialized.",
            ))
        }
    }
}
