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

use crate::{ClassTag, Error, Id, PCTag};
use num::{FromPrimitive, PrimInt};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::mem;

pub const LONG_FLAG: u8 = 0x1f;
pub const MAX_SHORT: u8 = LONG_FLAG - 1;
pub const MORE_FLAG: u8 = 0x80;
pub const CLASS_MASK: u8 = 0xc0;
pub const PC_MASK: u8 = 0x20;

/// `IdRef` is a wrapper of `[u8]` representing Identifier.
///
/// The user can access the inner slice via method [`as_bytes`] or [`as_mut_bytes`]
///
/// This struct is `Unsized`, and the user will usually use a reference to it.
///
/// [`as_bytes`]: Self::as_bytes
/// [`as_mut_bytes`]: Self::as_mut_bytes
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
    /// Parses `bytes` starting with identifier and tries to provide a reference to `IdRef`.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::IdRef;
    ///
    /// // &[0] represents 'EOC'.
    /// let bytes: &[u8] = &[0];
    /// let idref = IdRef::parse(bytes).unwrap();
    /// assert_eq!(IdRef::eoc(), idref);
    ///
    /// // The result is not changed if (an) extra octet(s) is added at the end.
    /// let bytes: &[u8] = &[0, 1, 2];
    /// let idref = IdRef::parse(bytes).unwrap();
    /// assert_eq!(IdRef::eoc(), idref);
    /// ```
    pub fn parse(bytes: &[u8]) -> Result<&Self, Error> {
        let first = *bytes.get(0).ok_or(Error::UnTerminatedBytes)?;

        if first & LONG_FLAG != LONG_FLAG {
            // Short From
            return Ok(unsafe { IdRef::from_bytes_unchecked(&bytes[0..1]) });
        }

        let second = *bytes.get(1).ok_or(Error::UnTerminatedBytes)?;

        if second <= MAX_SHORT {
            // Short form will do.
            return Err(Error::RedundantBytes);
        }

        if second == MORE_FLAG {
            // The second octet is not necessary.
            return Err(Error::RedundantBytes);
        }

        // Find the last octet
        for i in 1..bytes.len() {
            if bytes[i] & MORE_FLAG != MORE_FLAG {
                return Ok(unsafe { IdRef::from_bytes_unchecked(&bytes[0..=i]) });
            }
        }

        // The last octet is not found.
        Err(Error::UnTerminatedBytes)
    }

    /// Parses `bytes` starting with identifier, and tries to provide a mutable reference to
    /// `IdRef`.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef};
    ///
    /// let bytes: &mut [u8] = &mut [0];
    ///
    /// {
    ///     let idref = IdRef::parse_mut(bytes).unwrap();
    ///     // Update idref
    ///     idref.set_class(ClassTag::Private);
    /// }
    ///
    /// // 'bytes' is updcated as well.
    /// assert_eq!(bytes[0], ClassTag::Private as u8);
    ///
    /// // The result is not changed if (an) extra octet(s) is added at the end.
    /// let bytes: &mut [u8] = &mut [0, 1, 2, 3];
    /// let idref = IdRef::parse_mut(bytes).unwrap();
    /// assert_eq!(IdRef::eoc(), idref);
    /// ```
    pub fn parse_mut(bytes: &mut [u8]) -> Result<&mut Self, Error> {
        let ret = Self::parse(bytes)?;
        let ptr = (ret as *const Self) as *mut Self;
        unsafe { Ok(&mut *ptr) }
    }

    /// Provides a reference from `bytes` without any check.
    /// `bytes` must not include any extra octets.
    ///
    /// If it is not sure whether `bytes` is valid octets as an identifer, use [`parse`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if the format of `bytes` is not right.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::IdRef;
    ///
    /// // '&[0]' represents 'EOC'.
    /// let bytes: &[u8] = &[0];
    /// let idref = unsafe { IdRef::from_bytes_unchecked(bytes) };
    /// assert_eq!(IdRef::eoc(), idref);
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
    /// The behaviour is undefined if the format of `bytes` is not right.
    ///
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef};
    ///
    /// let bytes: &mut [u8] = &mut [0];
    ///
    /// {
    ///     let idref = unsafe { IdRef::from_mut_bytes_unchecked(bytes) };
    ///
    ///     // Update idref
    ///     idref.set_class(ClassTag::Application);
    /// }
    ///
    /// // 'bytes' is updated as well.
    /// assert_eq!(bytes[0], ClassTag::Application as u8);
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
    /// assert_eq!(0x00, id.number().unwrap());
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
    /// assert_eq!(0x01, id.number().unwrap());
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
    /// assert_eq!(0x02, id.number().unwrap());
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
    /// assert_eq!(0x03, id.number().unwrap());
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
    /// assert_eq!(0x03, id.number().unwrap());
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
    /// assert_eq!(0x04, id.number().unwrap());
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
    /// assert_eq!(0x04, id.number().unwrap());
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
    /// assert_eq!(0x05, id.number().unwrap());
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
    /// assert_eq!(0x06, id.number().unwrap());
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
    /// assert_eq!(0x07, id.number().unwrap());
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
    /// assert_eq!(0x08, id.number().unwrap());
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
    /// assert_eq!(0x09, id.number().unwrap());
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
    /// assert_eq!(0x0a, id.number().unwrap());
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
    /// assert_eq!(0x0b, id.number().unwrap());
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
    /// assert_eq!(0x0c, id.number().unwrap());
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
    /// assert_eq!(0x0c, id.number().unwrap());
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
    /// assert_eq!(0x0d, id.number().unwrap());
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
    /// assert_eq!(0x10, id.number().unwrap());
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
    /// assert_eq!(0x11, id.number().unwrap());
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
    /// assert_eq!(0x12, id.number().unwrap());
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
    /// assert_eq!(0x12, id.number().unwrap());
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
    /// assert_eq!(0x13, id.number().unwrap());
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
    /// assert_eq!(0x13, id.number().unwrap());
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
    /// assert_eq!(0x14, id.number().unwrap());
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
    /// assert_eq!(0x14, id.number().unwrap());
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
    /// assert_eq!(0x15, id.number().unwrap());
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
    /// assert_eq!(0x15, id.number().unwrap());
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
    /// assert_eq!(0x16, id.number().unwrap());
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
    /// assert_eq!(0x16, id.number().unwrap());
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
    /// assert_eq!(0x17, id.number().unwrap());
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
    /// assert_eq!(0x17, id.number().unwrap());
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
    /// assert_eq!(0x18, id.number().unwrap());
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
    /// assert_eq!(0x18, id.number().unwrap());
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
    /// assert_eq!(0x19, id.number().unwrap());
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
    /// assert_eq!(0x19, id.number().unwrap());
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
    /// assert_eq!(0x1a, id.number().unwrap());
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
    /// assert_eq!(0x1a, id.number().unwrap());
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
    /// assert_eq!(0x1b, id.number().unwrap());
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
    /// assert_eq!(0x1b, id.number().unwrap());
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
    /// assert_eq!(0x1c, id.number().unwrap());
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
    /// assert_eq!(0x1c, id.number().unwrap());
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
    /// assert_eq!(0x1d, id.number().unwrap());
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
    /// assert_eq!(0x1d, id.number().unwrap());
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
    /// assert_eq!(0x1e, id.number().unwrap());
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
    /// assert_eq!(0x1e, id.number().unwrap());
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
        self.eq(other.borrow())
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
    /// // Id of Universal Integer is [0x02].
    /// assert_eq!(IdRef::integer().len(), 1);
    ///
    /// let bytes: &[u8] = &[0xff, 0xff, 0x00];
    /// let id = IdRef::parse(bytes).unwrap();
    /// assert_eq!(id.len(), bytes.len());
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

    /// Returns `true` if `self` is 'Universal' class, or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8);
    /// assert_eq!(true, id.is_universal());
    /// ```
    pub fn is_universal(&self) -> bool {
        let first = self.bytes[0];
        first & CLASS_MASK == ClassTag::Universal as u8
    }

    /// Returns `true` if `self` is 'Application' class, or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Application, PCTag::Primitive, 0_u8);
    /// assert_eq!(true, id.is_application());
    /// ```
    pub fn is_application(&self) -> bool {
        let first = self.bytes[0];
        first & CLASS_MASK == ClassTag::Application as u8
    }

    /// Returns `true` if `self` is 'Context Specific' class, or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::ContextSpecific, PCTag::Primitive, 0_u8);
    /// assert_eq!(true, id.is_context_specific());
    /// ```
    pub fn is_context_specific(&self) -> bool {
        let first = self.bytes[0];
        first & CLASS_MASK == ClassTag::ContextSpecific as u8
    }

    /// Returns `true` if `self` is 'Private' class, or `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Private, PCTag::Primitive, 0_u8);
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
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8);
    /// assert_eq!(PCTag::Primitive, id.pc());
    ///
    /// let id = Id::new(ClassTag::Application, PCTag::Constructed, 1_u8);
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
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8);
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
    /// let id = Id::new(ClassTag::Universal, PCTag::Constructed, 0_u8);
    /// assert_eq!(true, id.is_constructed());
    /// ```
    pub fn is_constructed(&self) -> bool {
        let first = self.bytes[0];
        first & PC_MASK == PCTag::Constructed as u8
    }

    /// Returns the number of `self` unless overflow.
    ///
    /// Type `T` should be a built-in primitive integer type (e.g., u8, i32, isize, i128...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, IdRef, PCTag};
    /// use std::ops::Deref;
    ///
    /// let id = Id::new(ClassTag::Application, PCTag::Primitive, 49_u8);
    /// let idref: &IdRef = id.deref();
    /// assert_eq!(49, idref.number().unwrap());
    /// ```
    pub fn number<T>(&self) -> Result<T, Error>
    where
        T: PrimInt + FromPrimitive,
    {
        debug_assert!(0 < self.len());

        if self.bytes.len() == 1 {
            let ret = self.bytes[0] & LONG_FLAG;
            Ok(T::from_u8(ret).unwrap())
        } else {
            debug_assert_eq!(self.bytes[0] & LONG_FLAG, LONG_FLAG);

            let mask: u8 = !MORE_FLAG;
            let mut ret = T::from_u8(self.as_ref()[1] & mask).unwrap();

            for &octet in self.as_ref()[2..].iter() {
                let shft_mul = T::from_u8(128).ok_or(Error::OverFlow)?;
                ret = ret.checked_mul(&shft_mul).ok_or(Error::OverFlow)?;
                ret = ret + T::from_u8(octet & mask).unwrap();
            }

            Ok(ret)
        }
    }

    /// Update the class tag of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, IdRef};
    ///
    /// // Creates a '&mut IdRef' representing 'Universal Integer'.
    /// let mut bytes = Vec::from(IdRef::integer().as_ref());
    /// let idref = IdRef::parse_mut(&mut bytes).unwrap();
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

    /// Update the PC tag of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{PCTag, IdRef};
    ///
    /// // Creates a '&mut IdRef' representing 'Universal Integer'.
    /// let mut bytes = Vec::from(IdRef::integer().as_ref());
    /// let idref = IdRef::parse_mut(&mut bytes).unwrap();
    ///
    /// assert_eq!(PCTag::Primitive, idref.pc());
    ///
    /// idref.set_pc(PCTag::Constructed);
    /// assert_eq!(PCTag::Constructed, idref.pc());
    /// ```
    pub fn set_pc(&mut self, pc: PCTag) {
        let bytes = &mut self.bytes;

        const MASK: u8 = 0xdf;
        bytes[0] &= MASK;
        bytes[0] |= pc as u8;
    }
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

    #[test]
    fn parse_ok() {
        for &cl in CLASSES {
            for &pc in PCS {
                // 1 byte
                {
                    let first = cl as u8 + pc as u8 + 0;
                    let bytes: &[u8] = &[first];
                    let id = IdRef::parse(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());

                    let first = cl as u8 + pc as u8 + 0x1e;
                    let bytes: &[u8] = &[first];
                    let id = IdRef::parse(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());
                }

                let first = cl as u8 + pc as u8 + 0x1f;

                // 2 bytes
                {
                    let bytes: &[u8] = &[first, 0x1f];
                    let id = IdRef::parse(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());

                    let bytes: &[u8] = &[first, 0x7f];
                    let id = IdRef::parse(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());
                }

                // len bytes
                for len in 3..20 {
                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0x80);
                    }
                    bytes[1] = 0x81;
                    bytes[len - 1] = 0x00;

                    let bytes: &[u8] = &bytes;
                    let id = IdRef::parse(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());

                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0xff);
                    }
                    bytes[len - 1] = 0x7f;

                    let bytes: &[u8] = &bytes;
                    let id = IdRef::parse(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());
                }
            }
        }
    }

    #[test]
    fn parse_redundant() {
        for &cl in CLASSES {
            for &pc in PCS {
                let first = cl as u8 + pc as u8 + 0x1f;

                // 2 bytes
                {
                    let bytes: &[u8] = &[first, 0x00];
                    let e = IdRef::parse(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);

                    let bytes: &[u8] = &[first, 0x1e];
                    let e = IdRef::parse(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);
                }

                // len bytes
                for len in 3..20 {
                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0x80);
                    }
                    bytes[len - 1] = 0x00;

                    let bytes: &[u8] = &bytes;
                    let e = IdRef::parse(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);

                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0xff);
                    }
                    bytes[1] = 0x80;
                    bytes[len - 1] = 0x7f;

                    let bytes: &[u8] = &bytes;
                    let e = IdRef::parse(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);
                }
            }
        }
    }

    #[test]
    fn parse_unterminated() {
        // Empty
        {
            let bytes: &[u8] = &[];
            let e = IdRef::parse(bytes).unwrap_err();
            assert_eq!(Error::UnTerminatedBytes, e);
        }

        for &cl in CLASSES {
            for &pc in PCS {
                let first = cl as u8 + pc as u8 + 0x1f;

                // 1 bytes
                {
                    let bytes: &[u8] = &[first];
                    let e = IdRef::parse(bytes).unwrap_err();
                    assert_eq!(Error::UnTerminatedBytes, e);
                }

                // len bytes
                for len in 2..20 {
                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0x80);
                    }
                    bytes[1] = 0x81;

                    let bytes: &[u8] = &bytes;
                    let e = IdRef::parse(bytes).unwrap_err();
                    assert_eq!(Error::UnTerminatedBytes, e);

                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0xff);
                    }

                    let bytes: &[u8] = &bytes;
                    let e = IdRef::parse(bytes).unwrap_err();
                    assert_eq!(Error::UnTerminatedBytes, e);
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
                        let mut id = Id::new(cl0, pc, i);
                        id.set_class(cl1);

                        assert_eq!(cl1, id.class());
                        assert_eq!(pc, id.pc());
                        assert_eq!(Ok(i), id.number());
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
                        let mut id = Id::new(cl, pc0, i);
                        id.set_pc(pc1);

                        assert_eq!(cl, id.class());
                        assert_eq!(pc1, id.pc());
                        assert_eq!(Ok(i), id.number());
                    }
                }
            }
        }
    }
}
