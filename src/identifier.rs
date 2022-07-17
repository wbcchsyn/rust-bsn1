// Copyright 2021 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause"
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
//
//
// Redistribution and use in source and binary forms, with or without modification, are permitted
// provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice, this
//    list of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
// INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

use crate::{Buffer, Error};
use core::convert::TryFrom;
use core::mem;
use core::ops::Deref;
use num::cast::AsPrimitive;
use num::{FromPrimitive, PrimInt, Unsigned};
use std::borrow::Borrow;

/// `ClassTag` represents Tag class of identifier.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClassTag {
    /// Universal Tag
    Universal = 0x00,
    /// Application Tag
    Application = 0x40,
    /// Context-Specific Tag
    ContextSpecific = 0x80,
    /// Private Tag
    Private = 0xc0,
}

/// `PCTag` represents Primitive/Constructed flag of identifier.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PCTag {
    /// Primitive data type.
    Primitive = 0x00,
    /// Constructed data type.
    Constructed = 0x20,
}

/// `IdRef` is a wrapper of `[u8]` represents Identifier.
///
/// This struct is `Unsized` , and user will usually use a reference to it.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdRef {
    bytes: [u8],
}

impl IdRef {
    const LONG_FLAG: u8 = 0x1f;
    const MAX_SHORT: u8 = Self::LONG_FLAG - 1;
    const MORE_FLAG: u8 = 0x80;
}

impl<'a> TryFrom<&'a [u8]> for &'a IdRef {
    type Error = Error;

    /// Parses `bytes` starts with identifier and tries to build a new instance.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// This function is same to [`IdRef::from_bytes`] .
    ///
    /// [`IdRef::from_bytes`]: #method.from_bytes
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved so far, but this
    /// functions returns `Ok` .
    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        IdRef::from_bytes(bytes)
    }
}

impl<'a> TryFrom<&'a mut [u8]> for &'a mut IdRef {
    type Error = Error;

    /// Parses `bytes` starts with identifier and tries to build a new instance.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// This function is same to [`IdRef::from_bytes_mut`] .
    ///
    /// [`IdRef::from_bytes`]: #method.from_bytes_mut
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved so far, but this
    /// functions returns `Ok` .
    fn try_from(bytes: &'a mut [u8]) -> Result<Self, Self::Error> {
        IdRef::from_bytes_mut(bytes)
    }
}

/// Ommits the extra octets at the end of `bytes` and returns octets just one 'ASN.1 Identifier.'
///
/// # Safety
///
/// The behavior is undefined if `bytes` does not starts with 'ASN.1 Identifier.'
#[inline]
pub unsafe fn shrink_to_fit_unchecked(bytes: &[u8]) -> &[u8] {
    if bytes[0] & IdRef::LONG_FLAG != IdRef::LONG_FLAG {
        &bytes[0..1]
    } else {
        let mut i = 1;
        loop {
            if bytes[i] & IdRef::MORE_FLAG != IdRef::MORE_FLAG {
                return &bytes[..=i];
            }

            i += 1;
        }
    }
}

impl IdRef {
    /// Parses `bytes` starts with identifier and tries to build a new instance.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// This function is same to [`<&IdRef>::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved so far, but this
    /// functions returns `Ok` .
    ///
    /// [`<&IdRef>::try_from`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, IdRef, PCTag};
    ///
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8);
    /// let idref = IdRef::from_bytes(id.as_ref() as &[u8]).unwrap();
    /// assert_eq!(id.as_ref() as &IdRef, idref);
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Result<&Self, Error> {
        let first = *bytes.get(0).ok_or(Error::UnTerminatedBytes)?;

        if first & IdRef::LONG_FLAG != IdRef::LONG_FLAG {
            // Short From
            return Ok(unsafe { IdRef::from_bytes_unchecked(&bytes[0..1]) });
        }

        let second = *bytes.get(1).ok_or(Error::UnTerminatedBytes)?;

        if second <= IdRef::MAX_SHORT {
            // Short form will do.
            return Err(Error::RedundantBytes);
        }

        if second == IdRef::MORE_FLAG {
            // The second octet is not necessary.
            return Err(Error::RedundantBytes);
        }

        // Find the last octet
        for i in 1..bytes.len() {
            if bytes[i] & IdRef::MORE_FLAG != IdRef::MORE_FLAG {
                return Ok(unsafe { IdRef::from_bytes_unchecked(&bytes[0..=i]) });
            }
        }

        // The last octet is not found.
        Err(Error::UnTerminatedBytes)
    }

    /// Parses `bytes` starts with identifier and tries to build a new instance.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// This function is same to [`<&mut IdRef>::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved so far, but this
    /// functions returns `Ok` .
    ///
    /// [`<&mut IdRef>::try_from`]: #impl-TryFrom%3C%26%27a%20mut%20%5Bu8%5D%3E
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, IdRef, PCTag};
    ///
    /// let mut id0 = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8);
    /// let id1 = id0.clone();
    /// let idref = IdRef::from_bytes_mut(&mut id0).unwrap();
    /// assert_eq!(&id1 as &IdRef, idref);
    /// ```
    pub fn from_bytes_mut(bytes: &mut [u8]) -> Result<&mut Self, Error> {
        let ret = Self::from_bytes(bytes)?;
        let ptr = (ret as *const Self) as *mut Self;
        unsafe { Ok(&mut *ptr) }
    }
    /// Provides a reference from `bytes` without any sanitize.
    /// `bytes` must not include any extra octets.
    ///
    /// If it is not sure whether `bytes` is valid octets as an identifer or not, use [`TryFrom`]
    /// implementation or [`from_bytes`] instead.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if the format of `bytes` is not right.
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27a%20%5Bu8%5D%3E
    /// [`from_bytes`]: #method.from_bytes
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, IdRef, PCTag};
    ///
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8);
    /// let idref = unsafe { IdRef::from_bytes_unchecked(id.as_ref() as &[u8]) };
    /// assert_eq!(id.as_ref() as &IdRef, idref);
    /// ```
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        let ptr = bytes as *const [u8];
        let ptr = ptr as *const IdRef;
        &*ptr
    }

    /// Provides a reference to `IdRef` representing 'Universal EOC.'
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
    #[inline]
    pub fn eoc() -> &'static Self {
        const BYTES: [u8; 1] = [0x00];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Boolean.'
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
    #[inline]
    pub fn boolean() -> &'static Self {
        const BYTES: [u8; 1] = [0x01];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Integer.'
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn octet_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x24];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Null.'
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
    #[inline]
    pub fn null() -> &'static Self {
        const BYTES: [u8; 1] = [0x05];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Object Identifier.'
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
    #[inline]
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
    #[inline]
    pub fn object_descriptor() -> &'static Self {
        const BYTES: [u8; 1] = [0x07];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal External.'
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
    #[inline]
    pub fn external() -> &'static Self {
        const BYTES: [u8; 1] = [0x28];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Real.'
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
    #[inline]
    pub fn real() -> &'static Self {
        const BYTES: [u8; 1] = [0x09];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Enumerated.'
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
    #[inline]
    pub fn enumerated() -> &'static Self {
        const BYTES: [u8; 1] = [0x0a];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Embedded PDV.'
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn utf8_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x2c];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal UTF8 OID.'
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
    #[inline]
    pub fn relative_oid() -> &'static Self {
        const BYTES: [u8; 1] = [0x0d];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Sequence' or 'Universal Sequence
    /// of.'
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
    #[inline]
    pub fn sequence() -> &'static Self {
        const BYTES: [u8; 1] = [0x30];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }

    /// Provides a reference to `IdRef` representing 'Universal Set' or 'Universal Set of.'
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn bmp_string_constructed() -> &'static Self {
        const BYTES: [u8; 1] = [0x3e];
        unsafe { Self::from_bytes_unchecked(&BYTES as &[u8]) }
    }
}

impl AsRef<[u8]> for IdRef {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl Borrow<[u8]> for IdRef {
    #[inline]
    fn borrow(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for IdRef {
    type Owned = Id;

    fn to_owned(&self) -> Self::Owned {
        let buffer = Buffer::from(self.borrow());
        Self::Owned { buffer }
    }
}

impl PartialEq<Id> for IdRef {
    #[inline]
    fn eq(&self, other: &Id) -> bool {
        self == other.as_ref() as &IdRef
    }
}

impl IdRef {
    /// Returns `ClassTag` of `self` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0_u8);
    /// assert_eq!(ClassTag::Universal, id.class());
    ///
    /// let id = Id::new(ClassTag::Application, PCTag::Constructed, 1_u8);
    /// assert_eq!(ClassTag::Application, id.class());
    ///
    /// let id = Id::new(ClassTag::ContextSpecific, PCTag::Primitive, 2_u8);
    /// assert_eq!(ClassTag::ContextSpecific, id.class());
    ///
    /// let id = Id::new(ClassTag::Private, PCTag::Constructed, 3_u8);
    /// assert_eq!(ClassTag::Private, id.class());
    /// ```
    #[inline]
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

    /// Returns `true` if `self` is 'Universal' class, or `false` .
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
    #[inline]
    pub fn is_universal(&self) -> bool {
        let first = self.bytes[0];
        first & 0xc0 == ClassTag::Universal as u8
    }

    /// Returns `true` if `self` is 'Application' class, or `false` .
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
    #[inline]
    pub fn is_application(&self) -> bool {
        let first = self.bytes[0];
        first & 0xc0 == ClassTag::Application as u8
    }

    /// Returns `true` if `self` is 'Context Specific' class, or `false` .
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
    #[inline]
    pub fn is_context_specific(&self) -> bool {
        let first = self.bytes[0];
        first & 0xc0 == ClassTag::ContextSpecific as u8
    }

    /// Returns `true` if `self` is 'Private' class, or `false` .
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
    #[inline]
    pub fn is_private(&self) -> bool {
        let first = self.bytes[0];
        first & 0xc0 == ClassTag::Private as u8
    }

    /// Returns the Primitive/Constructed flag of `self` .
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
    #[inline]
    pub fn pc(&self) -> PCTag {
        if self.is_primitive() {
            PCTag::Primitive
        } else {
            PCTag::Constructed
        }
    }

    /// Returns `true` if `self` is flagged as 'Primitive', or `false` .
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
    #[inline]
    pub fn is_primitive(&self) -> bool {
        let first = self.bytes[0];
        first & 0x20 == PCTag::Primitive as u8
    }

    /// Returns `true` if `self` is flagged as 'Constructed', or `false` .
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
    #[inline]
    pub fn is_constructed(&self) -> bool {
        let first = self.bytes[0];
        first & 0x20 == PCTag::Constructed as u8
    }

    /// Returns the number of `self` unless overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Application, PCTag::Primitive, 49_u8);
    /// assert_eq!(49, id.number().unwrap());
    /// ```
    #[inline]
    pub fn number(&self) -> Result<u128, Error> {
        if self.bytes.len() == 1 {
            let ret = self.bytes[0] & Self::LONG_FLAG;
            debug_assert!(ret != Self::LONG_FLAG);
            Ok(ret as u128)
        } else if 20 < self.bytes.len() {
            Err(Error::OverFlow)
        } else if self.bytes.len() == 20 && 0x83 < self.bytes[1] {
            Err(Error::OverFlow)
        } else {
            let num: u128 = self.bytes[1..].iter().fold(0, |acc, octet| {
                let octet = octet & !Self::MORE_FLAG;
                (acc << 7) + (octet as u128)
            });

            Ok(num)
        }
    }

    /// Provides a reference to the inner slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::IdRef;
    ///
    /// let id = IdRef::integer();
    /// assert_eq!(&[0x02], id.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// `Id` owns `IdRef` and represents Identifier.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id {
    buffer: Buffer,
}

impl TryFrom<&[u8]> for Id {
    type Error = Error;

    /// Parses `bytes` starts with identifier octets and tries to build a new instance.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// This function is same to [`from_bytes`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// functions returns `Ok` .
    ///
    /// [`from_bytes`]: #method.from_bytes
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        <&IdRef>::try_from(bytes).map(|idref| idref.to_owned())
    }
}

impl Id {
    /// Creates a new instance from `class` , `pc` , and `number` .
    ///
    /// type `T` should be the builtin primitive unsigned integer types
    /// (e.g., u8, u16, u32, u64, u128, usize.)
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved so far, but this
    /// function accepts such a number.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // Creates 'Universal Integer'
    /// let _id = Id::new(ClassTag::Universal, PCTag::Primitive, 2_u8);
    /// ```
    pub fn new<T>(class: ClassTag, pc: PCTag, number: T) -> Self
    where
        T: Unsigned + FromPrimitive + PrimInt + AsPrimitive<u8>,
    {
        let mut buffer = Buffer::new();

        if number <= T::from_u8(IdRef::MAX_SHORT).unwrap() {
            let o = class as u8 + pc as u8 + number.as_();
            unsafe { buffer.push(o) };
        } else {
            let len = (mem::size_of::<T>() * 8 - number.leading_zeros() as usize + 6) / 7 + 1;
            buffer.reserve(len);
            unsafe { buffer.set_len(len) };

            buffer[0] = class as u8 + pc as u8 + IdRef::LONG_FLAG;

            let mut num = number;
            for i in (1..len).rev() {
                let o = num.as_() | IdRef::MORE_FLAG;
                buffer[i] = o;
                num = num.unsigned_shr(7);
            }
            buffer[len - 1] &= !(IdRef::MORE_FLAG);
        }

        Self { buffer }
    }

    /// Parses `bytes` starts with identifier and tries to build a new instance.
    ///
    /// This function ignores the extra octet(s) at the end if any.
    ///
    /// This function is same to [`TryFrom::try_from`] .
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved so far, but this
    /// functions returns `Ok` .
    ///
    /// [`TryFrom::try_from`]: #impl-TryFrom%3C%26%27_%20%5Bu8%5D%3E
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Self::try_from(bytes)
    }

    /// Provides a reference from `bytes` without any sanitize.
    /// `bytes` must not include any extra octets.
    ///
    /// If it is not sure whether `bytes` is valid octets as an identifer or not, use [`TryFrom`]
    /// implementation or [`from_bytes`] instead.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if the format of `bytes` is not right.
    ///
    /// [`TryFrom`]: #impl-TryFrom%3C%26%27_%20%5Bu8%5D%3E
    /// [`from_bytes`]: #method.from_bytes
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        IdRef::from_bytes_unchecked(bytes).to_owned()
    }
}

impl AsRef<[u8]> for Id {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_ref()
    }
}

impl AsRef<IdRef> for Id {
    #[inline]
    fn as_ref(&self) -> &IdRef {
        self.deref()
    }
}

impl Borrow<[u8]> for Id {
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.buffer.borrow()
    }
}

impl Borrow<IdRef> for Id {
    #[inline]
    fn borrow(&self) -> &IdRef {
        self.deref()
    }
}

impl Deref for Id {
    type Target = IdRef;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { IdRef::from_bytes_unchecked(self.buffer.as_ref()) }
    }
}

impl PartialEq<IdRef> for Id {
    #[inline]
    fn eq(&self, other: &IdRef) -> bool {
        self.as_ref() as &IdRef == other
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
    fn try_from_ok() {
        for &cl in CLASSES {
            for &pc in PCS {
                // 1 byte
                {
                    let first = cl as u8 + pc as u8 + 0;
                    let bytes: &[u8] = &[first];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());

                    let first = cl as u8 + pc as u8 + 0x1e;
                    let bytes: &[u8] = &[first];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());
                }

                let first = cl as u8 + pc as u8 + 0x1f;

                // 2 bytes
                {
                    let bytes: &[u8] = &[first, 0x1f];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(bytes, id.as_ref());

                    let bytes: &[u8] = &[first, 0x7f];
                    let id = <&IdRef>::try_from(bytes).unwrap();
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

                    let bytes: &[u8] = bytes.as_ref();
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(bytes.as_ref(), id.as_ref());

                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0xff);
                    }
                    bytes[len - 1] = 0x7f;

                    let bytes: &[u8] = bytes.as_ref();
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(bytes.as_ref(), id.as_ref());
                }
            }
        }
    }

    #[test]
    fn try_from_redundant() {
        for &cl in CLASSES {
            for &pc in PCS {
                let first = cl as u8 + pc as u8 + 0x1f;

                // 2 bytes
                {
                    let bytes: &[u8] = &[first, 0x00];
                    let e = <&IdRef>::try_from(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);

                    let bytes: &[u8] = &[first, 0x1e];
                    let e = <&IdRef>::try_from(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);
                }

                // len bytes
                for len in 3..20 {
                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0x80);
                    }
                    bytes[len - 1] = 0x00;

                    let bytes: &[u8] = bytes.as_ref();
                    let e = <&IdRef>::try_from(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);

                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0xff);
                    }
                    bytes[1] = 0x80;
                    bytes[len - 1] = 0x7f;

                    let bytes: &[u8] = bytes.as_ref();
                    let e = <&IdRef>::try_from(bytes).unwrap_err();
                    assert_eq!(Error::RedundantBytes, e);
                }
            }
        }
    }

    #[test]
    fn try_from_unterminated() {
        // Empty
        {
            let bytes: &[u8] = &[];
            let e = <&IdRef>::try_from(bytes).unwrap_err();
            assert_eq!(Error::UnTerminatedBytes, e);
        }

        for &cl in CLASSES {
            for &pc in PCS {
                let first = cl as u8 + pc as u8 + 0x1f;

                // 1 bytes
                {
                    let bytes: &[u8] = &[first];
                    let e = <&IdRef>::try_from(bytes).unwrap_err();
                    assert_eq!(Error::UnTerminatedBytes, e);
                }

                // len bytes
                for len in 2..20 {
                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0x80);
                    }
                    bytes[1] = 0x81;

                    let bytes: &[u8] = bytes.as_ref();
                    let e = <&IdRef>::try_from(bytes).unwrap_err();
                    assert_eq!(Error::UnTerminatedBytes, e);

                    let mut bytes = vec![first];
                    for _ in 1..len {
                        bytes.push(0xff);
                    }

                    let bytes: &[u8] = bytes.as_ref();
                    let e = <&IdRef>::try_from(bytes).unwrap_err();
                    assert_eq!(Error::UnTerminatedBytes, e);
                }
            }
        }
    }

    #[test]
    fn number() {
        for &cl in CLASSES {
            for &pc in PCS {
                // 1 byte
                {
                    let num: u128 = 0;
                    let first = cl as u8 + pc as u8 + num as u8;
                    let bytes: &[u8] = &[first];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(num, id.number().unwrap());

                    let num: u128 = 30;
                    let first = cl as u8 + pc as u8 + num as u8;
                    let bytes: &[u8] = &[first];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(num, id.number().unwrap());
                }

                let first = cl as u8 + pc as u8 + 31;

                // 2 bytes
                {
                    let num: u128 = 0x1f;
                    let bytes: &[u8] = &[first, num as u8];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(num, id.number().unwrap());

                    let num: u128 = 0x7f;
                    let bytes: &[u8] = &[first, num as u8];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(num, id.number().unwrap());
                }

                // 3 bytes
                {
                    let num: u128 = 0x80;
                    let bytes: &[u8] = &[first, 0x81, 0x00];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(num, id.number().unwrap());

                    let num: u128 = 0x3fff;
                    let bytes: &[u8] = &[first, 0xff, 0x7f];
                    let id = <&IdRef>::try_from(bytes).unwrap();
                    assert_eq!(num, id.number().unwrap());
                }

                // max
                {
                    let mut bytes: [u8; 20] = [0xff; 20];
                    bytes[0] = first;
                    bytes[1] = 0x83;
                    bytes[19] = 0x7f;
                    let id = <&IdRef>::try_from(&bytes as &[u8]).unwrap();
                    assert_eq!(std::u128::MAX, id.number().unwrap());

                    let mut bytes: [u8; 20] = [0x80; 20];
                    bytes[0] = first;
                    bytes[1] = 0x84;
                    bytes[19] = 0x00;
                    let id = <&IdRef>::try_from(&bytes as &[u8]).unwrap();
                    assert_eq!(Error::OverFlow, id.number().unwrap_err());
                }
            }
        }
    }

    #[test]
    fn new() {
        for &cl in CLASSES {
            for &pc in PCS {
                for &num in &[
                    0,
                    30,
                    31,
                    0x7f,
                    0x80,
                    0x3fff,
                    0x8000,
                    0x1fffff,
                    std::u128::MAX,
                ] {
                    let id = Id::new(cl, pc, num);
                    let idref = <&IdRef>::try_from(id.as_ref() as &[u8]).unwrap();
                    assert_eq!(idref.as_ref(), id.as_ref() as &[u8]);
                }
            }
        }
    }

    #[test]
    fn id_new_u8() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in 0..=IdRef::MAX_SHORT {
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + i];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
                for i in (IdRef::MAX_SHORT + 1)..0x80 {
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, i];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
                for i in 0x80..=u8::MAX {
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, 0x81, i - 0x80];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }

    #[test]
    fn id_new_u16() {
        for &cl in CLASSES {
            for &pc in PCS {
                // Same to u8 (Check again.)
                {
                    for i in 0..=IdRef::MAX_SHORT {
                        let id = Id::new(cl, pc, i as u16);
                        let expected: &[u8] = &[cl as u8 + pc as u8 + i];
                        assert_eq!(id.as_ref() as &[u8], expected);
                    }
                    for i in (IdRef::MAX_SHORT + 1)..0x80 {
                        let id = Id::new(cl, pc, i as u16);
                        let expected: &[u8] = &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, i];
                        assert_eq!(id.as_ref() as &[u8], expected);
                    }
                    for i in 0x80..=u8::MAX {
                        let id = Id::new(cl, pc, i as u16);
                        let expected: &[u8] =
                            &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, 0x81, i - 0x80];
                        assert_eq!(id.as_ref() as &[u8], expected);
                    }
                }

                // u8::MAX + 1
                {
                    let i = u8::MAX as u16 + 1;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, 0x82, 0];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // i16::MAX
                {
                    let i = i16::MAX as u16;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] =
                        &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, 0x81, 0xff, 0x7f];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // i16::MAX + 1
                {
                    let i = i16::MAX as u16 + 1;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] =
                        &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, 0x82, 0x80, 0x00];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // u16::MAX
                {
                    let i = u16::MAX;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] =
                        &[cl as u8 + pc as u8 + IdRef::LONG_FLAG, 0x83, 0xff, 0x7f];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }

    #[test]
    fn id_new_u128() {
        for &cl in CLASSES {
            for &pc in PCS {
                // u64::MAX
                {
                    let i = u64::MAX as u128;
                    let id = Id::new(cl, pc, i);
                    let expected: &mut [u8] = &mut [0xff; 11];
                    expected[0] = cl as u8 + pc as u8 + IdRef::LONG_FLAG;
                    expected[1] = 0x81;
                    expected[10] = 0x7f;
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // u64::MAX + 1
                {
                    let i = u64::MAX as u128 + 1;
                    let id = Id::new(cl, pc, i);
                    let expected: &mut [u8] = &mut [0x80; 11];
                    expected[0] = cl as u8 + pc as u8 + IdRef::LONG_FLAG;
                    expected[1] = 0x82;
                    expected[10] = 0x00;
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // u128::MAX
                {
                    let i = u128::MAX;
                    let id = Id::new(cl, pc, i);
                    let expected: &mut [u8] = &mut [0xff; 20];
                    expected[0] = cl as u8 + pc as u8 + IdRef::LONG_FLAG;
                    expected[1] = 0x83;
                    expected[19] = 0x7f;
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }
}
