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
use core::ops::Deref;
use std::borrow::Borrow;

/// `ClassTag` is u8 enum for Tag class of Identifier in 'ASN.1.'
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

/// `PCTag` is u8 enum for Private/Constructed flag of Identifier in 'ASN.1.'
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PCTag {
    /// Primitive data type.
    Primitive = 0x00,
    /// Constructed data type.
    Constructed = 0x20,
}

/// `IdRef` represents Identifier octets in 'ASN.1.'
///
/// This struct is `Unsized` , so usually thay use a reference to it.
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

    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
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
}

impl IdRef {
    /// Builds instance from `bytes` without any sanitize.
    /// `bytes` must not include any extra octets.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if the format of `bytes` is not right.
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        let ptr = bytes as *const [u8];
        let ptr = ptr as *const IdRef;
        &*ptr
    }
}

impl AsRef<[u8]> for IdRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl Borrow<[u8]> for IdRef {
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

impl IdRef {
    /// Returns `ClassTag` of `self` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0);
    /// assert_eq!(ClassTag::Universal, id.class());
    ///
    /// let id = Id::new(ClassTag::Application, PCTag::Constructed, 1);
    /// assert_eq!(ClassTag::Application, id.class());
    ///
    /// let id = Id::new(ClassTag::ContextSpecific, PCTag::Primitive, 2);
    /// assert_eq!(ClassTag::ContextSpecific, id.class());
    ///
    /// let id = Id::new(ClassTag::Private, PCTag::Constructed, 3);
    /// assert_eq!(ClassTag::Private, id.class());
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

    /// Returns `true` if `self` is 'Universal' class, or `false` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // 'Id' implements 'Deref<Target = IdRef>'.
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0);
    /// assert_eq!(true, id.is_universal());
    /// ```
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
    /// let id = Id::new(ClassTag::Application, PCTag::Primitive, 0);
    /// assert_eq!(true, id.is_application());
    /// ```
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
    /// let id = Id::new(ClassTag::ContextSpecific, PCTag::Primitive, 0);
    /// assert_eq!(true, id.is_context_specific());
    /// ```
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
    /// let id = Id::new(ClassTag::Private, PCTag::Primitive, 0);
    /// assert_eq!(true, id.is_private());
    /// ```
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
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0);
    /// assert_eq!(PCTag::Primitive, id.pc());
    ///
    /// let id = Id::new(ClassTag::Application, PCTag::Constructed, 1);
    /// assert_eq!(PCTag::Constructed, id.pc());
    /// ```
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
    /// let id = Id::new(ClassTag::Universal, PCTag::Primitive, 0);
    /// assert_eq!(true, id.is_primitive());
    /// ```
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
    /// let id = Id::new(ClassTag::Universal, PCTag::Constructed, 0);
    /// assert_eq!(true, id.is_constructed());
    /// ```
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
    /// let id = Id::new(ClassTag::Application, PCTag::Primitive, 49);
    /// assert_eq!(49, id.number().unwrap());
    /// ```
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
}

/// `Id` owns `IdRef` and represents Identifier octets in 'ASN.1.'
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id {
    buffer: Buffer,
}

impl TryFrom<&[u8]> for Id {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        <&IdRef>::try_from(bytes).map(|idref| idref.to_owned())
    }
}

impl Id {
    /// Creates a new instance from `class` , `pc` , and `number` .
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// // Creates 'Universal Integer'
    /// let _id = Id::new(ClassTag::Universal, PCTag::Primitive, 2);
    /// ```
    pub fn new(class: ClassTag, pc: PCTag, number: u128) -> Self {
        let mut buffer = Buffer::new();

        if number <= IdRef::MAX_SHORT as u128 {
            let o = class as u8 + pc as u8 + number as u8;
            buffer.push(o);
        } else {
            let len = ((128 - number.leading_zeros() + 6) / 7 + 1) as usize;
            buffer.reserve(len);
            unsafe { buffer.set_len(len) };

            buffer[0] = class as u8 + pc as u8 + IdRef::LONG_FLAG;

            let mut num = number;
            for i in (1..len).rev() {
                let o = (num as u8) | IdRef::MORE_FLAG;
                buffer[i] = o;
                num >>= 7;
            }
            buffer[len - 1] &= !(IdRef::MORE_FLAG);
        }

        Self { buffer }
    }
}

impl Borrow<[u8]> for Id {
    fn borrow(&self) -> &[u8] {
        self.buffer.borrow()
    }
}

impl Borrow<IdRef> for Id {
    fn borrow(&self) -> &IdRef {
        self.deref()
    }
}

impl Deref for Id {
    type Target = IdRef;

    fn deref(&self) -> &Self::Target {
        unsafe { IdRef::from_bytes_unchecked(self.buffer.as_ref()) }
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
                    assert_eq!(u128::MAX, id.number().unwrap());

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
                for &num in &[0, 30, 31, 0x7f, 0x80, 0x3fff, 0x8000, 0x1fffff, u128::MAX] {
                    let id = Id::new(cl, pc, num);
                    let idref = <&IdRef>::try_from(id.as_ref()).unwrap();
                    assert_eq!(idref.as_ref(), id.as_ref());
                }
            }
        }
    }
}
