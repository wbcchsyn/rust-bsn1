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

use crate::identifier_ref::{LONG_FLAG, MAX_SHORT, MORE_FLAG};
use crate::{Buffer, ClassTag, Error, IdNumber, IdRef, PCTag};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::io::Read;
use std::mem;
use std::ops::{Deref, DerefMut};

/// `Id` owns [`IdRef`] and represents 'Identifier'.
///
/// The structure of `Id` is similar to that of `Vec<u8>`.
///
/// The user can access the inner [`IdRef`] via the `Deref` and `DerefMut` implementations.
///
/// [`IdRef`]: crate::IdRef
#[derive(Debug, Clone, Eq, Ord, Hash)]
pub struct Id {
    buffer: Buffer,
}

impl From<&'_ IdRef> for Id {
    fn from(idref: &'_ IdRef) -> Self {
        Self {
            buffer: Buffer::from(idref.as_ref()),
        }
    }
}

impl Id {
    /// Creates a new instance from `class` , `pc` , and `number`.
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores the rule.
    /// For example, number 15 (0x0f) is reserved for now,
    /// but this function accepts such a number without any error.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Id, IdRef};
    ///
    /// let idref = IdRef::integer();
    /// let id = Id::new(idref.class(), idref.pc(), idref.number().unwrap());
    /// assert_eq!(idref, &id);
    /// ```
    pub fn new(class: ClassTag, pc: PCTag, number: IdNumber) -> Self {
        let mut buffer = Buffer::new();
        let number = number.get();

        if number <= MAX_SHORT as u128 {
            let o = class as u8 + pc as u8 + number as u8;
            unsafe { buffer.push(o) };
        } else {
            let long_flag = class as u8 + pc as u8 + LONG_FLAG;

            const BITS_PER_BYTES: usize = 8;
            const BITS_BUT_MORE_FLAG_PER_BYTES: usize = 7;
            let number_bits_len =
                mem::size_of_val(&number) * BITS_PER_BYTES - number.leading_zeros() as usize;
            let number_bytes_len =
                (number_bits_len + BITS_BUT_MORE_FLAG_PER_BYTES - 1) / BITS_BUT_MORE_FLAG_PER_BYTES;

            let len = number_bytes_len + mem::size_of_val(&long_flag);
            buffer.reserve(len);
            unsafe { buffer.set_len(len) };

            buffer[0] = long_flag;

            let mut num = number;
            for i in (1..len).rev() {
                let o = num as u8 | MORE_FLAG;
                buffer[i] = o;
                num >>= 7;
            }
            buffer[len - 1] ^= MORE_FLAG;
        }

        Self { buffer }
    }

    /// Parses `readable` starting with identifier and tries to build a new instance.
    ///
    /// This function ignores extra octet(s) at the end if any.
    ///
    /// # Performance
    ///
    /// This function is not so efficient compared with [`IdRef::parse`].
    /// If you have a slice of serialized bytes, use [`IdRef::parse`]
    /// and then call [`ToOwned::to_owned`] instead.
    ///
    /// [`IdRef::parse`]: IdRef::parse
    /// [`ToOwned::to_owned`]: std::borrow::ToOwned::to_owned
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores the rule.
    /// For example, number 15 (0x0f) is reserved for now,
    /// but this functions returns `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Id, IdRef};
    ///
    /// // Serialize an 'identifier' representing 'utf8-string'
    /// let id = IdRef::utf8_string();
    /// let mut serialized = Vec::from(id.as_ref());
    ///
    /// // Deserialize it.
    /// let deserialized = Id::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(id, &deserialized);
    ///
    /// // Extra octets at the end does not affect the result.
    /// serialized.push(0);
    /// serialized.push(1);
    /// let deserialized = Id::parse(&mut &serialized[..]).unwrap();
    /// assert_eq!(id, &deserialized);
    ///
    /// // We can use `IdRef::parse` instead. It is more efficient.
    /// let deserialized: Id = IdRef::parse(&mut &serialized[..]).map(ToOwned::to_owned).unwrap();
    /// assert_eq!(id, &deserialized);
    /// ```
    pub fn parse<R: Read>(readable: &mut R) -> Result<Self, Error> {
        let mut buffer = Buffer::new();
        unsafe { crate::identifier_ref::parse_id(readable, &mut buffer)? };
        Ok(Self { buffer })
    }

    /// Provides a reference from `bytes` without any check.
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as an identifer, use [`parse`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if the format of `bytes` is bad as 'identifier octets'.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Id, IdRef};
    ///
    /// let id = IdRef::eoc();
    /// let serialized = id.as_ref();
    /// let deserialized = unsafe { Id::from_bytes_unchecked(serialized) };
    /// assert_eq!(deserialized, id);
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        Self {
            buffer: Buffer::from(bytes),
        }
    }
}

impl AsRef<[u8]> for Id {
    fn as_ref(&self) -> &[u8] {
        self.buffer.as_bytes()
    }
}

impl AsRef<IdRef> for Id {
    fn as_ref(&self) -> &IdRef {
        self.deref()
    }
}

impl AsMut<IdRef> for Id {
    fn as_mut(&mut self) -> &mut IdRef {
        self.deref_mut()
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
        unsafe { IdRef::from_bytes_unchecked(self.buffer.as_bytes()) }
    }
}

impl DerefMut for Id {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { mem::transmute(self.buffer.as_mut_bytes()) }
    }
}

impl<T> PartialEq<T> for Id
where
    T: Borrow<IdRef>,
{
    fn eq(&self, other: &T) -> bool {
        self.deref() == other.borrow()
    }
}

impl<T> PartialOrd<T> for Id
where
    T: Borrow<IdRef>,
{
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        self.deref().partial_cmp(other.borrow())
    }
}

impl Id {
    /// Update the number of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Id, PCTag};
    ///
    /// let mut id = Id::new(ClassTag::Private, PCTag::Primitive, 13_u8.into());
    /// assert_eq!(id.number().unwrap(), 13_u8.into());
    ///
    /// id.set_number(34_u8.into());
    /// assert_eq!(id.number().unwrap(), 34_u8.into());
    /// ```
    pub fn set_number(&mut self, num: IdNumber) {
        let num = num.get();

        if num <= MAX_SHORT as u128 {
            let o = self.class() as u8 + self.pc() as u8 + num as u8;
            self.buffer[0] = o;
            unsafe { self.buffer.set_len(1) };
        } else {
            let long_flag = self.class() as u8 + self.pc() as u8 + LONG_FLAG;

            const BITS_PER_BYTES: usize = 8;
            const BITS_BUT_MORE_FLAG_PER_BYTES: usize = 7;
            let number_bits_len =
                mem::size_of_val(&num) * BITS_PER_BYTES - num.leading_zeros() as usize;
            let number_bytes_len =
                (number_bits_len + BITS_BUT_MORE_FLAG_PER_BYTES - 1) / BITS_BUT_MORE_FLAG_PER_BYTES;

            let len = number_bytes_len + mem::size_of_val(&long_flag);
            if self.buffer.len() < len {
                self.buffer.reserve(len - self.buffer.len());
            }
            unsafe { self.buffer.set_len(len) };

            self.buffer[0] = long_flag;

            let mut n = num;
            for i in (1..len).rev() {
                let o = n as u8 | MORE_FLAG;
                self.buffer[i] = o;
                n >>= 7;
            }
            self.buffer[len - 1] &= !(MORE_FLAG);
            debug_assert!(n == 0);
        }
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
    fn number_ok() {
        for &cl in CLASSES {
            for &pc in PCS {
                // u8
                for i in 0..=u8::MAX {
                    let id = Id::new(cl, pc, i.into());
                    assert_eq!(Ok(i.into()), id.number());
                }
                // u16
                for i in 0..=u16::MAX {
                    let id = Id::new(cl, pc, i.into());
                    assert_eq!(Ok(i.into()), id.number());
                }
                // u128::MAX
                {
                    let id = Id::new(cl, pc, u128::MAX.into());
                    assert_eq!(Ok(u128::MAX.into()), id.number());
                }
            }
        }
    }

    #[test]
    fn number_overflow() {
        for &cl in CLASSES {
            for &pc in PCS {
                let mut bytes = [0x80; 20];
                bytes[0] = cl as u8 | pc as u8 | LONG_FLAG;
                bytes[1] = 0x84;
                bytes[19] = 0x00;
                let mut bytes = &bytes as &[u8];
                let id = Id::parse(&mut bytes).unwrap();
                assert!(id.number().is_err());
            }
        }
    }

    #[test]
    fn new() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in (0..=u16::MAX as u128).chain(Some(u128::MAX)) {
                    let id = Id::new(cl, pc, i.into());
                    assert_eq!(cl, id.class());
                    assert_eq!(pc, id.pc());
                    assert_eq!(Ok(i.into()), id.number());

                    let idref = IdRef::parse(&mut id.as_ref()).unwrap();
                    assert_eq!(id, idref);
                }
            }
        }
    }

    #[test]
    fn new_1_byte() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in 0..=MAX_SHORT {
                    let id = Id::new(cl, pc, i.into());
                    let expected = &[cl as u8 + pc as u8 + i];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }

    const MAX_2_BYTES: u128 = 0x7f;

    #[test]
    fn new_2_byte() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in (MAX_SHORT as u128 + 1)..=MAX_2_BYTES {
                    let id = Id::new(cl, pc, i.into());
                    let expected = &[cl as u8 + pc as u8 + LONG_FLAG, i as u8];
                    assert_eq!(expected[1] & MORE_FLAG, 0);
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }

    const MAX_3_BYTES: u128 = 0x3fff;

    #[test]
    fn new_3_byte() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in (MAX_2_BYTES + 1)..=MAX_3_BYTES {
                    let id = Id::new(cl, pc, i.into());
                    let expected = &[
                        cl as u8 + pc as u8 | LONG_FLAG,
                        (i >> 7) as u8 | MORE_FLAG,
                        i as u8 & !MORE_FLAG,
                    ];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }

    const MAX_4_BYTES: u128 = 0x1fffff;

    #[test]
    fn new_4_bytes() {
        for &cl in CLASSES {
            for &pc in PCS {
                for &i in &[MAX_3_BYTES + 1, MAX_4_BYTES] {
                    let id = Id::new(cl, pc, i.into());
                    let expected = &[
                        cl as u8 + pc as u8 + LONG_FLAG,
                        (i >> 14) as u8 | MORE_FLAG,
                        (i >> 7) as u8 | MORE_FLAG,
                        i as u8 & !MORE_FLAG,
                    ];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }

    #[test]
    fn new_max_bytes() {
        for &cl in CLASSES {
            for &pc in PCS {
                let id = Id::new(cl, pc, u128::MAX.into());

                let mut bytes = Vec::from(id.as_ref() as &[u8]);
                let mut num = u128::MAX;

                // Check the last octet.
                assert_eq!(bytes.pop().unwrap(), num as u8 & !MORE_FLAG);
                num >>= 7;

                // Check the middle octets.
                while 1 < bytes.len() {
                    assert_eq!(bytes.pop().unwrap(), num as u8 | MORE_FLAG);
                    num >>= 7;
                }

                assert_eq!(num, 0);
                assert_eq!(bytes.pop().unwrap(), cl as u8 + pc as u8 + LONG_FLAG);
            }
        }
    }

    #[test]
    fn set_number() {
        for &cl in CLASSES {
            for &pc in PCS {
                let mut id = Id::new(cl, pc, 0_u8.into());

                for i in 0..=u16::MAX {
                    id.set_number(i.into());
                    assert_eq!(cl, id.class());
                    assert_eq!(pc, id.pc());
                    assert_eq!(Ok(i.into()), id.number());
                }

                for i in (0..=u16::MAX).rev() {
                    id.set_number(i.into());
                    assert_eq!(cl, id.class());
                    assert_eq!(pc, id.pc());
                    assert_eq!(Ok(i.into()), id.number());
                }
            }
        }
    }
}
