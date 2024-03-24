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

        if attribute.is_transparent() && data.fields.len() != 1 {
            return Err(syn::Error::new_spanned(
                attribute.transparent_token(),
                "The field count of transparent struct must be 1.",
            ));
        }

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
        let field = self.transparent_field_var();
        let field_attribute = self.transparent_field_attribute();

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

        let id = self.id_slice()?;
        Ok(quote! { #Result::Ok(#id.len()) })
    }

    #[allow(non_snake_case)]
    pub fn id_len_transparent(&self) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Serialize = quote! { ::bsn1_serde::ser::Serialize };
        let field = self.transparent_field_var();
        let field_attribute = self.transparent_field_attribute();

        if let Some(into_ty) = field_attribute.into_type() {
            let Clone = quote! { ::std::clone::Clone };
            let Into = quote! { ::std::convert::Into };
            let this = quote! { bsn1_macro_1704044765_this };

            Ok(quote! {{
                let #this = #Clone::clone(#field);
                let #this: #into_ty = #Into::into(#this);
                #Serialize::id_len(&#this)
            }})
        } else if let Some(path) = field_attribute.to_path() {
            let this = quote! { bsn1_macro_1706411411_this };

            Ok(quote! {{
                let #this = #path(#field);
                #Serialize::id_len(&#this)
            }})
        } else {
            Ok(quote! { #Serialize::id_len(#field) })
        }
    }

    pub fn id_slice(&self) -> syn::Result<TokenStream> {
        // This method should not be called if converting annottation is specified.
        assert!(self.attribute().into_type().is_none());
        assert!(self.attribute().from_type().is_none());
        assert!(self.attribute().to_path().is_none());
        assert!(self.attribute().try_from_type().is_none());

        // This method should not be called if `transparent` is specified.
        assert!(self.attribute().is_transparent() == false);

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
    pub fn write_der_contents_transparent(&self, buffer: &TokenStream) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Serialize = quote! { ::bsn1_serde::ser::Serialize };
        let field = self.transparent_field_var();
        let field_attribute = self.transparent_field_attribute();

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
    pub fn der_contents_len_transparent(&self) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Serialize = quote! { ::bsn1_serde::ser::Serialize };
        let field = self.transparent_field_var();
        let field_attribute = self.transparent_field_attribute();

        if let Some(into_ty) = field_attribute.into_type() {
            let Clone = quote! { ::std::clone::Clone };
            let Into = quote! { ::std::convert::Into };
            let this = quote! { bsn1_macro_1704043457_this };

            Ok(quote! {{
                let #this = #Clone::clone(#field);
                let #this: #into_ty = #Into::into(#this);
                #Serialize::der_contents_len(&#this)
            }})
        } else if let Some(to_path) = field_attribute.to_path() {
            let this = quote! { bsn1_macro_1705721776_this };

            Ok(quote! {{
                let #this = #to_path(#field);
                #Serialize::der_contents_len(&#this)
            }})
        } else {
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
    pub fn from_ber_transparent(
        &self,
        id: &TokenStream,
        length: &TokenStream,
        contents: &TokenStream,
    ) -> syn::Result<TokenStream> {
        assert!(self.attribute().is_transparent());

        let Result = quote! { ::std::result::Result };
        let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

        let field_attribute = self.transparent_field_attribute();
        let ty = self.ty();
        let tmp_val = quote! { #Deserialize::from_ber(#id, #length, #contents)? };

        let inner = if let Some(from_ty) = field_attribute.from_type() {
            let From = quote! { ::std::convert::From };
            quote! { #From::<#from_ty>::from(#tmp_val) }
        } else if let Some(try_from_ty) = field_attribute.try_from_type() {
            let TryFrom = quote! { ::std::convert::TryFrom };
            let Anyhow = quote! { ::anyhow::Error };
            let Error = quote! { ::bsn1_serde::macro_alias::Error };

            quote! {
                #TryFrom::<#try_from_ty>::try_from(#tmp_val).map_err(|err| {
                    #Error::from(#Anyhow::new(err))
                })?
            }
        } else {
            tmp_val
        };

        match self.fields() {
            syn::Fields::Named(_) => {
                let field_ident = self.transparent_field_ident();
                Ok(quote! {
                    #Result::Ok(#ty { #field_ident: #inner })
                })
            }
            syn::Fields::Unnamed(_) => Ok(quote! {
                #Result::Ok(#ty ( #inner ))
            }),
            syn::Fields::Unit => unreachable!(),
        }
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
                return #Result::Err(#Error::InvalidContents);
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

        let Result = quote! { ::std::result::Result };
        let Deserialize = quote! { ::bsn1_serde::de::Deserialize };

        let field_attribute = self.transparent_field_attribute();
        let ty = self.ty();
        let tmp_val = quote! { #Deserialize::from_der(#id, #contents)? };

        let inner = if let Some(from_ty) = field_attribute.from_type() {
            let From = quote! { ::std::convert::From };
            quote! { #From::<#from_ty>::from(#tmp_val) }
        } else if let Some(try_from_ty) = field_attribute.try_from_type() {
            let TryFrom = quote! { ::std::convert::TryFrom };
            let Anyhow = quote! { ::anyhow::Error };
            let Error = quote! { ::bsn1_serde::macro_alias::Error };

            quote! {
                #TryFrom::<#try_from_ty>::try_from(#tmp_val).map_err(|err| {
                    #Error::from(#Anyhow::new(err))
                })?
            }
        } else {
            tmp_val
        };

        match self.fields() {
            syn::Fields::Named(_) => {
                let field_ident = self.transparent_field_ident();
                Ok(quote! { #Result::Ok(#ty { #field_ident: #inner }) })
            }
            syn::Fields::Unnamed(_) => Ok(quote! {
                #Result::Ok(#ty ( #inner ))
            }),
            syn::Fields::Unit => unreachable!(),
        }
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

    fn transparent_field_ident(&self) -> TokenStream {
        assert!(self.attribute().is_transparent());

        let mut field_idents = self.field_idents();
        assert!(field_idents.len() == 1);
        field_idents.pop().unwrap()
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

    fn transparent_field_var(&self) -> TokenStream {
        assert!(self.attribute().is_transparent());

        let mut field_vars = self.field_vars();
        assert!(field_vars.len() == 1);
        field_vars.pop().unwrap()
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

    fn transparent_field_attribute(&self) -> &Attribute {
        assert!(self.attribute().is_transparent());

        let field_attributes = self.field_attributes();
        assert!(field_attributes.len() == 1);

        field_attributes.first().unwrap()
    }
}
