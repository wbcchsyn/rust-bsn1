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
use proc_macro2::TokenStream;
use quote::quote;

pub enum DataContainer {
    DataStruct {
        attribute: Attribute,
        field_attributes: Vec<Attribute>,
        data_structure: syn::DataStruct,
    },
    Variant {
        attribute: Attribute,
        field_attributes: Vec<Attribute>,
        variant: syn::Variant,
    },
}

impl TryFrom<(Attribute, syn::DataStruct)> for DataContainer {
    type Error = syn::Error;

    fn try_from((attribute, data): (Attribute, syn::DataStruct)) -> Result<Self, Self::Error> {
        let mut field_attributes = Vec::new();
        for field in data.fields.iter() {
            field_attributes.push(Attribute::try_from(&field.attrs[..])?);
        }

        Ok(Self::DataStruct {
            attribute,
            field_attributes,
            data_structure: data,
        })
    }
}

impl TryFrom<syn::Variant> for DataContainer {
    type Error = syn::Error;

    fn try_from(value: syn::Variant) -> Result<Self, Self::Error> {
        let attribute = Attribute::try_from(&value.attrs[..])?;
        let mut field_attributes = Vec::new();
        for field in value.fields.iter() {
            field_attributes.push(Attribute::try_from(&field.attrs[..])?);
        }

        Ok(Self::Variant {
            attribute,
            field_attributes,
            variant: value,
        })
    }
}

impl DataContainer {
    #[allow(non_snake_case)]
    pub fn write_id(&self, buffer: &TokenStream) -> syn::Result<TokenStream> {
        let Error = quote! { ::bsn1_serde::macro_alias::Error };
        let Write = quote! { ::std::io::Write };
        let Result = quote! { ::std::result::Result };

        let id = self.id_slice()?;
        Ok(quote! {{
            #Write.write_all(#buffer, &#id).map_err(#Error::from);
            #Result::Ok(())
        }})
    }

    fn id_slice(&self) -> syn::Result<TokenStream> {
        const SEQUENCE: u8 = 0x30;

        match self.attribute().id(SEQUENCE) {
            Some(id) => Ok(id),
            None => Ok(quote! { [#SEQUENCE] }),
        }
    }

    fn attribute(&self) -> &Attribute {
        match self {
            Self::DataStruct { attribute, .. } => attribute,
            Self::Variant { attribute, .. } => attribute,
        }
    }
}
