// Copyright 2021-2023 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of bsn1
//
//  bsn1 is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  bsn1 is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with bsn1.  If not, see <http://www.gnu.org/licenses/>.
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

use crate::{ClassTag, Error, Id, IdNumber, PCTag};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::io::{Read, Write};
use std::mem;

pub const LONG_FLAG: u8 = 0x1f;
pub const MAX_SHORT: u8 = LONG_FLAG - 1;
pub const MORE_FLAG: u8 = 0x80;
pub const CLASS_MASK: u8 = 0xc0;
pub const PC_MASK: u8 = 0x20;

/// `IdRef` is a wrapper of `[u8]` representing Identifier.
///
/// The user can access the inner slice via `AsRef` implementation.
///
/// This struct is `Unsized`, and the user will usually use a reference to it.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdRef {
    bytes: [u8],
}

/// Ommits the extra octets at the end of `bytes` and returns octets just one 'ASN.1 Identifier.'
///
/// # Safety
///
/// The behaviour is undefined if `bytes` does not starts with 'ASN.1 Identifier.'
pub unsafe fn shrink_to_fit_unchecked(bytes: &[u8]) -> &[u8] {
    if bytes[0] & LONG_FLAG != LONG_FLAG {
        &bytes[0..1]
    } else {
        for i in 1.. {
            if bytes[i] & MORE_FLAG != MORE_FLAG {
                return &bytes[..=i];
            }
        }
        unreachable!();
    }
}

impl IdRef {
    /// Parses `bytes` starting with identifier octets and provides a reference to `IdRef`.
    ///
    /// This function ignores extra octet(s) at the end if any.
    ///
    /// On success, `bytes` will be updated to point the next octet of `IdRef`;
    /// otehrwise, `bytes` will not be updated.
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores the rule. For example, number 15 (0x0f) is reserved for now,
    /// but this functions returns `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::IdRef;
    ///
    /// // Serialize an 'identifier' representing 'utf8-string'
    /// let id = IdRef::utf8_string();
    /// let mut serialized = Vec::from(id.as_ref());
    ///
    /// // Deserialize.
    /// {
    ///     let mut serialized: &[u8] = &serialized[..];
    ///     let deserialized = IdRef::parse(&mut serialized).unwrap();
    ///     assert_eq!(id, deserialized);
    ///     assert_eq!(serialized.len(), 0);
    /// }
    ///
    /// // Extra octets at the end does not affect the result.
    /// serialized.push(0x00);
    /// serialized.push(0x01);
    /// {
    ///     let mut serialized: &[u8] = &serialized[..];
    ///     let deserialized = IdRef::parse(&mut serialized).unwrap();
    ///     assert_eq!(id, deserialized);
    ///     assert_eq!(serialized, &[0x00, 0x01]);
    /// }
    /// ```
    pub fn parse<'a>(bytes: &mut &'a [u8]) -> Result<&'a Self, Error> {
        let mut readable: &[u8] = bytes;

        unsafe {
            let len = parse_id(&mut readable, &mut std::io::sink())?;
            let ret = Self::from_bytes_unchecked(&bytes[..len]);

            *bytes = readable;
            Ok(ret)
        }
    }

    /// Parses `bytes` starting with identifier, and provides a mutable reference to `IdRef`.
    ///
    /// This function ignores extra octet(s) at the end if any.
    ///
    /// On success, `bytes` will be updated to point the next octet of `IdRef`;
    /// otehrwise, `bytes` will not be updated.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores the rule. For example, number 15 (0x0f) is reserved for now,
    /// but this functions returns `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef};
    ///
    /// // Serialize an 'identifier' representing 'utf8-string'
    /// let id = IdRef::utf8_string();
    /// let mut serialized = Vec::from(id.as_ref());
    ///
    /// // Deserialize.
    /// {
    ///     let mut serialized: &mut [u8] = &mut serialized[..];
    ///     let deserialized = IdRef::parse_mut(&mut serialized).unwrap();
    ///     assert_eq!(id, deserialized);
    ///     assert_eq!(serialized.len(), 0);
    ///
    ///     deserialized.set_class(ClassTag::Private);
    /// }
    ///
    /// // Now, `serialized` is changed.
    /// // Deserialize again, and the result is not same to before.
    /// {
    ///     let mut serialized: &mut [u8] = &mut serialized[..];
    ///     let deserialized = IdRef::parse_mut(&mut serialized).unwrap();
    ///     assert_ne!(id, deserialized);
    ///     assert_eq!(serialized, &serialized[..]);
    /// }
    /// ```
    pub fn parse_mut<'a>(bytes: &mut &'a mut [u8]) -> Result<&'a mut Self, Error> {
        let read_bytes = {
            let mut readable: &[u8] = *bytes;
            unsafe { parse_id(&mut readable, &mut std::io::sink())? }
        };

        unsafe {
            let init_ptr = bytes.as_mut_ptr();
            let left_bytes = bytes.len() - read_bytes;
            *bytes = std::slice::from_raw_parts_mut(init_ptr.add(read_bytes), left_bytes);

            let read = std::slice::from_raw_parts_mut(init_ptr, read_bytes);
            Ok(Self::from_mut_bytes_unchecked(read))
        }
    }

    /// Provides a reference from `bytes` without any check.
    /// `bytes` must not include any extra octets.
    ///
    /// If it is not sure whether `bytes` is valid octets as an identifer, use [`parse`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if the format of `bytes` is invalid as 'identifier octets'.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::IdRef;
    ///
    /// let id = IdRef::eoc();
    /// let serialized = id.as_ref();
    /// let deserialized = unsafe { IdRef::from_bytes_unchecked(serialized) };
    /// assert_eq!(id, deserialized);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        mem::transmute(bytes)
    }

    /// Provides a mutable reference from `bytes` without any check.
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as an identifer,
    /// use [`parse_mut`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if the format of `bytes` is bad as 'identifier octets'.
    ///
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef};
    ///
    /// // Serialize and deserialize `id` representing 'EOC'.
    /// let id = IdRef::eoc();
    /// let mut serialized: Vec<u8> = Vec::from(id.as_ref());
    /// let deserialized = unsafe { IdRef::from_mut_bytes_unchecked(&mut serialized[..]) };
    ///
    /// // `deserialized` is same to `id` and the class is 'universal'.
    /// assert_eq!(id, deserialized);
    /// assert_eq!(ClassTag::Universal, deserialized.class());
    ///
    /// // Update deserialized
    /// deserialized.set_class(ClassTag::Application);
    ///
    /// assert_ne!(id, deserialized);
    /// assert_eq!(ClassTag::Application, deserialized.class());
    ///
    /// // `serialized` was changed as well.
    /// assert_ne!(id.as_ref(), &serialized[..]);
    /// ```
    pub unsafe fn from_mut_bytes_unchecked(bytes: &mut [u8]) -> &mut Self {
        mem::transmute(bytes)
    }

    /// Provides a reference to `IdRef` representing 'Universal EOC'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::eoc();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x00, id.number().unwrap().get());
    /// ```
    pub fn eoc() -> &'static Self {
        const BYTES: [u8; 1] = [0x00];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Boolean'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::boolean();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x01, id.number().unwrap().get());
    /// ```
    pub fn boolean() -> &'static Self {
        const BYTES: [u8; 1] = [0x01];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Integer'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::integer();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x02, id.number().unwrap().get());
    /// ```
    pub fn integer() -> &'static Self {
        const BYTES: [u8; 1] = [0x02];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Bit String' with primitive flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::bit_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x03, id.number().unwrap().get());
    /// ```
    pub fn bit_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x03];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Bit String' with constructed flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::bit_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x03, id.number().unwrap().get());
    /// ```
    pub fn bit_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x23];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Octet String' with primitive flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::octet_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x04, id.number().unwrap().get());
    /// ```
    pub fn octet_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x04];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Octet String' with constructed flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::octet_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x04, id.number().unwrap().get());
    /// ```
    pub fn octet_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x24];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Null'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::null();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x05, id.number().unwrap().get());
    /// ```
    pub fn null() -> &'static Self {
        const BYTES: [u8; 1] = [0x05];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Object Identifier'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::object_identifier();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x06, id.number().unwrap().get());
    /// ```
    pub fn object_identifier() -> &'static Self {
        const BYTES: [u8; 1] = [0x06];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Object Descriptor' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::object_descriptor();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x07, id.number().unwrap().get());
    /// ```
    pub fn object_descriptor() -> &'static Self {
        const BYTES: [u8; 1] = [0x07];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal External'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::external();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x08, id.number().unwrap().get());
    /// ```
    pub fn external() -> &'static Self {
        const BYTES: [u8; 1] = [0x28];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Real'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::real();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x09, id.number().unwrap().get());
    /// ```
    pub fn real() -> &'static Self {
        const BYTES: [u8; 1] = [0x09];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Enumerated'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::enumerated();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x0a, id.number().unwrap().get());
    /// ```
    pub fn enumerated() -> &'static Self {
        const BYTES: [u8; 1] = [0x0a];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Embedded PDV'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::embedded_pdv();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x0b, id.number().unwrap().get());
    /// ```
    pub fn embedded_pdv() -> &'static Self {
        const BYTES: [u8; 1] = [0x2b];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal UTF8 String' with primitive flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::utf8_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x0c, id.number().unwrap().get());
    /// ```
    pub fn utf8_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x0c];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal UTF8 String' with constructed flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::utf8_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x0c, id.number().unwrap().get());
    /// ```
    pub fn utf8_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x2c];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal UTF8 OID'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::relative_oid();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x0d, id.number().unwrap().get());
    /// ```
    pub fn relative_oid() -> &'static Self {
        const BYTES: [u8; 1] = [0x0d];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Sequence' or 'Universal Sequence
    /// of'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::sequence();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x10, id.number().unwrap().get());
    /// ```
    pub fn sequence() -> &'static Self {
        const BYTES: [u8; 1] = [0x30];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Set' or 'Universal Set of'.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::set();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x11, id.number().unwrap().get());
    /// ```
    pub fn set() -> &'static Self {
        const BYTES: [u8; 1] = [0x31];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Numeric String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::numeric_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x12, id.number().unwrap().get());
    /// ```
    pub fn numeric_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x12];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Numeric String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::numeric_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x12, id.number().unwrap().get());
    /// ```
    pub fn numeric_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x32];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Printable String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::printable_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x13, id.number().unwrap().get());
    /// ```
    pub fn printable_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x13];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Printable String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::printable_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x13, id.number().unwrap().get());
    /// ```
    pub fn printable_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x33];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal T61 String' with primitive flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::t61_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x14, id.number().unwrap().get());
    /// ```
    pub fn t61_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x14];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal T61 String' with constructed flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::t61_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x14, id.number().unwrap().get());
    /// ```
    pub fn t61_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x34];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Videotex String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::videotex_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x15, id.number().unwrap().get());
    /// ```
    pub fn videotex_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x15];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Videotex String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::videotex_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x15, id.number().unwrap().get());
    /// ```
    pub fn videotex_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x35];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal IA5 String' with primitive flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::ia5_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x16, id.number().unwrap().get());
    /// ```
    pub fn ia5_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x16];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal IA5 String' with constructed flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::ia5_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x16, id.number().unwrap().get());
    /// ```
    pub fn ia5_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x36];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal UTC Time' with primitive flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::utc_time();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x17, id.number().unwrap().get());
    /// ```
    pub fn utc_time() -> &'static Self {
        const BYTES: [u8; 1] = [0x17];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal UTC Time' with constructed flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::utc_time_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x17, id.number().unwrap().get());
    /// ```
    pub fn utc_time_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x37];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Generalized Time' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::generalized_time();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x18, id.number().unwrap().get());
    /// ```
    pub fn generalized_time() -> &'static Self {
        const BYTES: [u8; 1] = [0x18];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Generalized Time' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::generalized_time_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x18, id.number().unwrap().get());
    /// ```
    pub fn generalized_time_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x38];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Graphic String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::graphic_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x19, id.number().unwrap().get());
    /// ```
    pub fn graphic_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x19];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Graphic String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::graphic_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x19, id.number().unwrap().get());
    /// ```
    pub fn graphic_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x39];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Visible String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::visible_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x1a, id.number().unwrap().get());
    /// ```
    pub fn visible_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x1a];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Visible String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::visible_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x1a, id.number().unwrap().get());
    /// ```
    pub fn visible_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x3a];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal General String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::general_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x1b, id.number().unwrap().get());
    /// ```
    pub fn general_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x1b];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal General String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::general_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x1b, id.number().unwrap().get());
    /// ```
    pub fn general_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x3b];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Universal String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::universal_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x1c, id.number().unwrap().get());
    /// ```
    pub fn universal_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x1c];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Universal String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::universal_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x1c, id.number().unwrap().get());
    /// ```
    pub fn universal_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x3c];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Character String' with primitive
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::character_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x1d, id.number().unwrap().get());
    /// ```
    pub fn character_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x1d];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Character String' with constructed
    /// flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::character_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x1d, id.number().unwrap().get());
    /// ```
    pub fn character_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x3d];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal BMP String' with primitive flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::bmp_string();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Primitive, id.pc());
    /// assert_eq!(0x1e, id.number().unwrap().get());
    /// ```
    pub fn bmp_string() -> &'static Self {
        const BYTES: [u8; 1] = [0x1e];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal BMP String' with constructed flag.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef, PCTag};
    ///
    /// let id = IdRef::bmp_string_constructed();
    ///
    /// assert_eq!(ClassTag::Universal, id.class());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// assert_eq!(0x1e, id.number().unwrap().get());
    /// ```
    pub fn bmp_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x3e];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }
}

impl AsRef<[u8]> for IdRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for IdRef {
    type Owned = Id;

    fn to_owned(&self) -> Self::Owned {
        unsafe { Self::Owned::from_bytes_unchecked(self.as_ref()) }
    }
}

impl<T> PartialEq<T> for IdRef
where
    T: Borrow<IdRef>,
{
    fn eq(&self, other: &T) -> bool {
        self == other.borrow()
    }
}

impl<T> PartialOrd<T> for IdRef
where
    T: Borrow<IdRef>,
{
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        self.partial_cmp(other.borrow())
    }
}

impl IdRef {
    /// Returns the byte count of the inner bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::IdRef;
    ///
    /// // Id of Universal Integer is [0x02]. It is 1 byte long.
    /// let id = IdRef::integer();
    /// assert_eq!(id.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        return self.as_ref().len();
    }

    /// Returns the `ClassTag` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef};
    ///
    /// // 'EOC' is defined as Universal class.
    /// let eoc = IdRef::eoc();
    /// assert_eq!(ClassTag::Universal, eoc.class());
    /// ```
    pub fn class(&self) -> ClassTag {
        if self.is_universal() {
            ClassTag::Universal
        } else if self.is_application() {
            ClassTag::Application
        } else if self.is_context_specific() {
            ClassTag::ContextSpecific
        } else {
            ClassTag::Private
        }
    }

    /// Returns `true` if `self` is 'Universal class', or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8.into());
    /// assert_eq!(true, id.is_universal());
    /// ```
    pub fn is_universal(&self) -> bool {
        let first = self.bytes[0];
        first & CLASS_MASK == ClassTag::Universal as u8
    }

    /// Returns `true` if `self` is 'Application class', or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Application, PCTag::Primitive, 0_u8.into());
    /// assert_eq!(true, id.is_application());
    /// ```
    pub fn is_application(&self) -> bool {
        let first = self.bytes[0];
        first & CLASS_MASK == ClassTag::Application as u8
    }

    /// Returns `true` if `self` is 'Context Specific class', or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::ContextSpecific, PCTag::Primitive, 0_u8.into());
    /// assert_eq!(true, id.is_context_specific());
    /// ```
    pub fn is_context_specific(&self) -> bool {
        let first = self.bytes[0];
        first & CLASS_MASK == ClassTag::ContextSpecific as u8
    }

    /// Returns `true` if `self` is 'Private class', or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Private, PCTag::Primitive, 0_u8.into());
    /// assert_eq!(true, id.is_private());
    /// ```
    pub fn is_private(&self) -> bool {
        let first = self.bytes[0];
        first & CLASS_MASK == ClassTag::Private as u8
    }

    /// Returns the Primitive/Constructed flag of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8.into());
    /// assert_eq!(PCTag::Primitive, id.pc());
    ///
    /// let id = Id::new(ClassTag::Application, PCTag::Constructed, 1_u8.into());
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// ```
    pub fn pc(&self) -> PCTag {
        if self.is_primitive() {
            PCTag::Primitive
        } else {
            PCTag::Constructed
        }
    }

    /// Returns `true` if `self` is flagged as 'Primitive', or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8.into());
    /// assert_eq!(true, id.is_primitive());
    /// ```
    pub fn is_primitive(&self) -> bool {
        let first = self.bytes[0];
        first & PC_MASK == PCTag::Primitive as u8
    }

    /// Returns `true` if `self` is flagged as 'Constructed', or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Constructed, 0_u8.into());
    /// assert_eq!(true, id.is_constructed());
    /// ```
    pub fn is_constructed(&self) -> bool {
        let first = self.bytes[0];
        first & PC_MASK == PCTag::Constructed as u8
    }

    /// Returns the number of `self` unless overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, IdRef, PCTag};
    /// use std::ops::Deref;
    ///
    /// let id = Id::new(ClassTag::Application, PCTag::Primitive, 49_u8.into());
    /// let idref: &IdRef = id.deref();
    /// assert_eq!(49, idref.number().unwrap().get());
    /// ```
    pub fn number(&self) -> Result<IdNumber, Error> {
        debug_assert!(0 < self.len());

        if self.bytes.len() == 1 {
            let ret = self.bytes[0] & LONG_FLAG;
            Ok(ret.into())
        } else {
            debug_assert_eq!(self.bytes[0] & LONG_FLAG, LONG_FLAG);

            let mut ret: u128 = 0;

            for &octet in self.as_ref()[1..].iter() {
                const MASK: u8 = !MORE_FLAG;
                const SHIFT_MUL: u128 = 128;
                ret = ret.checked_mul(SHIFT_MUL).ok_or(Error::OverFlow)?;
                ret += (octet & MASK) as u128;
            }

            Ok(ret.into())
        }
    }

    /// Update the class of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef};
    ///
    /// // Creates a '&mut IdRef' representing 'Universal Integer'.
    /// let mut bytes = Vec::from(IdRef::integer().as_ref());
    /// let idref = IdRef::parse_mut(&mut &mut bytes[..]).unwrap();
    ///
    /// assert_eq!(ClassTag::Universal, idref.class());
    ///
    /// idref.set_class(ClassTag::Application);
    /// assert_eq!(ClassTag::Application, idref.class());
    /// ```
    pub fn set_class(&mut self, cls: ClassTag) {
        let bytes = &mut self.bytes;

        bytes[0] &= !CLASS_MASK;
        bytes[0] |= cls as u8;
    }

    /// Update the Primitive/Constructed flag of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{PCTag, IdRef};
    ///
    /// let id = IdRef::integer();
    /// let mut serialized = Vec::from(id.as_ref());
    /// let deserialized = IdRef::parse_mut(&mut &mut serialized[..]).unwrap();
    ///
    /// // 'Integer' is primitive.
    /// assert_eq!(PCTag::Primitive, deserialized.pc());
    ///
    /// // Force to change into constructed.
    /// deserialized.set_pc(PCTag::Constructed);
    /// assert_eq!(PCTag::Constructed, deserialized.pc());
    /// ```
    pub fn set_pc(&mut self, pc: PCTag) {
        let bytes = &mut self.bytes;

        const MASK: u8 = !PC_MASK;
        bytes[0] &= MASK;
        bytes[0] |= pc as u8;
    }
}

/// Parses `readable` starting with 'id', writes the parsed bytes to `writeable`, and returns the
/// parsed bytes count.
///
/// # Safety
///
/// The behavior is undefined if `writeable` is closed or broken before this function returns.
/// `writeable` should be `std::io::Sink` or `Buffer`.
pub unsafe fn parse_id<R: Read, W: Write>(
    readable: &mut R,
    writeable: &mut W,
) -> Result<usize, Error> {
    use crate::misc::{read_u8, write_u8};

    let first = read_u8(readable)?;
    write_u8(writeable, first)?;

    if first & LONG_FLAG != LONG_FLAG {
        // short form
        return Ok(1);
    }

    let mut octet = read_u8(readable)?;

    if octet <= MAX_SHORT {
        // Short form will do.
        return Err(Error::RedundantBytes);
    }
    if octet == MORE_FLAG {
        // The second octet is not necessary.
        return Err(Error::RedundantBytes);
    }

    for i in 2.. {
        write_u8(writeable, octet)?;

        if octet & MORE_FLAG != MORE_FLAG {
            return Ok(i);
        }

        octet = read_u8(readable)?;
    }

    unreachable!();
}

#[cfg(test)]
mod tests {
    use super::*;

    const CLASSES: &[ClassTag] = &[
        ClassTag::Universal,
        ClassTag::Application,
        ClassTag::ContextSpecific,
        ClassTag::Private,
    ];
    const PCS: &[PCTag] = &[PCTag::Primitive, PCTag::Constructed];

    const MAX_2BYTES: u8 = 0x7f;
    const MAX_3BYTES: u32 = 0x3fff;

    #[test]
    fn parse_1byte_ok() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in 0..=MAX_SHORT {
                    let first = cl as u8 + pc as u8 + i;
                    let mut bytes: &[u8] = &[first];
                    let id = IdRef::parse(&mut bytes).unwrap();

                    assert_eq!(id.as_ref(), &[first]);
                    assert_eq!(bytes.len(), 0);
                }
            }
        }
    }

    #[test]
    fn parse_2byte_ok() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in (MAX_SHORT + 1)..=MAX_2BYTES {
                    let first = cl as u8 + pc as u8 + LONG_FLAG;
                    let mut bytes: &[u8] = &[first, i];
                    let id = IdRef::parse(&mut bytes).unwrap();

                    assert_eq!(id.as_ref(), &[first, i]);
                    assert_eq!(bytes.len(), 0);
                }
            }
        }
    }

    #[test]
    fn parse_3byte_ok() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in (MAX_2BYTES as u32 + 1)..=MAX_3BYTES {
                    let first = cl as u8 + pc as u8 + LONG_FLAG;
                    let j = (i >> 7) as u8 | MORE_FLAG;
                    let k = i as u8 & !MORE_FLAG;

                    let mut bytes: &[u8] = &[first, j, k];
                    let id = IdRef::parse(&mut bytes).unwrap();

                    assert_eq!(id.as_ref(), &[first, j, k]);
                    assert_eq!(bytes.len(), 0);
                }
            }
        }
    }

    #[test]
    fn parse_4byte_ok() {
        for &cl in CLASSES {
            for &pc in PCS {
                let i = MAX_3BYTES + 1;
                let first = cl as u8 + pc as u8 + LONG_FLAG;
                let j = (i >> 14) as u8 | MORE_FLAG;
                let k = (i >> 7) as u8 | MORE_FLAG;
                let l = i as u8 & !MORE_FLAG;

                let mut bytes: &[u8] = &[first, j, k, l];
                let id = IdRef::parse(&mut bytes).unwrap();

                assert_eq!(id.as_ref(), &[first, j, k, l]);
                assert_eq!(bytes.len(), 0);
            }
        }
    }

    #[test]
    fn parse_2byte_redundant() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in 0..=MAX_SHORT {
                    let first = cl as u8 + pc as u8 + LONG_FLAG;
                    let mut bytes: &[u8] = &[first, i];
                    let e = IdRef::parse(&mut bytes);

                    assert_eq!(Err(Error::RedundantBytes), e);
                    assert_eq!(bytes, &[first, i]);
                }
            }
        }
    }

    #[test]
    fn parse_3byte_redundant() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in 0..=u8::MAX {
                    let first = cl as u8 + pc as u8 + LONG_FLAG;
                    let mut bytes: &[u8] = &[first, 0x00, i];
                    let e = IdRef::parse(&mut bytes);

                    assert_eq!(Err(Error::RedundantBytes), e);
                    assert_eq!(bytes, &[first, 0x00, i]);
                }
            }
        }
    }

    #[test]
    fn parse_empty_unterminated() {
        let mut bytes: &[u8] = &[];
        let e = IdRef::parse(&mut bytes);
        assert_eq!(Err(Error::UnTerminatedBytes), e);
        assert_eq!(bytes, &[]);
    }

    #[test]
    fn parse_1byte_unterminated() {
        for &cl in CLASSES {
            for &pc in PCS {
                let first = cl as u8 + pc as u8 + LONG_FLAG;
                let mut bytes: &[u8] = &[first];

                let e = IdRef::parse(&mut bytes);
                assert_eq!(Err(Error::UnTerminatedBytes), e);
                assert_eq!(bytes, &[first]);
            }
        }
    }

    #[test]
    fn parse_2byte_unterminated() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in (MORE_FLAG + 1)..=u8::MAX {
                    let first = cl as u8 + pc as u8 + LONG_FLAG;
                    let mut bytes: &[u8] = &[first, i];

                    let e = IdRef::parse(&mut bytes);
                    assert_eq!(Err(Error::UnTerminatedBytes), e);
                    assert_eq!(bytes, &[first, i]);
                }
            }
        }
    }

    #[test]
    fn parse_3byte_unterminated() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in (MORE_FLAG + 1)..=u8::MAX {
                    for j in MORE_FLAG..=u8::MAX {
                        let first = cl as u8 + pc as u8 + LONG_FLAG;
                        let mut bytes: &[u8] = &[first, i, j];

                        let e = IdRef::parse(&mut bytes);
                        assert_eq!(Err(Error::UnTerminatedBytes), e);
                        assert_eq!(bytes, &[first, i, j]);
                    }
                }
            }
        }
    }

    #[test]
    fn set_class() {
        for &cl0 in CLASSES {
            for &pc in PCS {
                for &cl1 in CLASSES {
                    for i in 0..=u16::MAX {
                        let mut id = Id::new(cl0, pc, i.into());
                        id.set_class(cl1);

                        assert_eq!(cl1, id.class());
                        assert_eq!(pc, id.pc());
                        assert_eq!(Ok(i.into()), id.number());
                    }
                }
            }
        }
    }

    #[test]
    fn set_pc() {
        for &cl in CLASSES {
            for &pc0 in PCS {
                for &pc1 in PCS {
                    for i in 0..=u16::MAX {
                        let mut id = Id::new(cl, pc0, i.into());
                        id.set_pc(pc1);

                        assert_eq!(cl, id.class());
                        assert_eq!(pc1, id.pc());
                        assert_eq!(Ok(i.into()), id.number());
                    }
                }
            }
        }
    }
}
