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
use crate::{Buffer, ClassTag, Error, IdRef, PCTag};
use num::cast::AsPrimitive;
use num::{FromPrimitive, PrimInt, Unsigned};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::mem;
use std::ops::{Deref, DerefMut};

/// `Id` owns [`IdRef`] and represents 'Identifier'.
///
/// The structure of `Id` is similar to that of `Vec<u8>`.
///
/// The user can access the [`IdRef`] via the [`Deref`] and [`DerefMut`] implementations, and
/// the inner slice via [`IdRef`].
///
/// [`IdRef`]: struct.IdRef.html
/// [`Deref`]: #impl-Deref-for-Id
/// [`DerefMut`]: #impl-DerefMut-for-Id
#[derive(Debug, Clone, Eq, Ord, Hash)]
pub struct Id {
    buffer: Buffer,
}

impl Id {
    /// Creates a new instance from `class` , `pc` , and `number`.
    ///
    /// type `T` should be a built-in primitive unsigned integer type
    /// (e.g., u8, u16, u32, u64, u128, usize.)
    ///
    /// # Warnings
    ///
    /// ASN.1 reserves some universal identifier numbers and they should not be used, however,
    /// this function ignores that. For example, number 15 (0x0f) is reserved for now, but this
    /// function accepts such a number.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Id, IdRef};
    ///
    /// let idref = IdRef::integer();
    /// let id = Id::new(idref.class(), idref.pc(), idref.number::<u64>().unwrap());
    /// assert_eq!(idref, &id);
    /// ```
    pub fn new<T>(class: ClassTag, pc: PCTag, number: T) -> Self
    where
        T: Unsigned + FromPrimitive + PrimInt + AsPrimitive<u8>,
    {
        let mut buffer = Buffer::new();

        if number <= T::from_u8(MAX_SHORT).unwrap() {
            let o = class as u8 + pc as u8 + number.as_();
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
                let o = num.as_() | MORE_FLAG;
                buffer[i] = o;
                num = num.unsigned_shr(7);
            }
            buffer[len - 1] &= !(MORE_FLAG);
        }

        Self { buffer }
    }

    /// Parses `bytes` starting with identifier and tries to build a new instance.
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
    /// use bsn1::Id;
    ///
    /// // &[0] represents 'Univedrsal EOC'.
    /// let bytes0: &[u8] = &[0];
    /// let id0 = Id::parse(bytes0).unwrap();
    ///
    /// // The extra octets at the end does not affect the result.
    /// let bytes1: &[u8] = &[0, 1, 2];
    /// let id1 = Id::parse(bytes1).unwrap();
    ///
    /// assert_eq!(id0, id1);
    /// ```
    pub fn parse(bytes: &[u8]) -> Result<Self, Error> {
        IdRef::parse(bytes).map(|idref| idref.to_owned())
    }

    /// Provides a reference from `bytes` without any check.
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as an identifer, use [`parse`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if the format of `bytes` is not right.
    ///
    /// [`parse`]: Self::parse
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
        self.deref().eq(other.borrow())
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
    /// let mut id = Id::new(ClassTag::Private, PCTag::Primitive, 13_u8);
    /// assert_eq!(id.number::<u8>().unwrap(), 13_u8);
    ///
    /// id.set_number(34_u8);
    /// assert_eq!(id.number::<u8>().unwrap(), 34_u8);
    /// ```
    pub fn set_number<T>(&mut self, num: T)
    where
        T: Unsigned + FromPrimitive + PrimInt + AsPrimitive<u8>,
    {
        if num <= T::from_u8(MAX_SHORT).unwrap() {
            let o = self.class() as u8 + self.pc() as u8 + num.as_();
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
                let o = n.as_() | MORE_FLAG;
                self.buffer[i] = o;
                n = n.unsigned_shr(7);
            }
            self.buffer[len - 1] &= !(MORE_FLAG);
            debug_assert!(n == T::from_u8(0).unwrap());
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
                // i8
                for i in 0..=i8::MAX {
                    let id = Id::new(cl, pc, i as u8);
                    assert_eq!(Ok(i), id.number());
                }
                // u8
                for i in 0..=u8::MAX {
                    let id = Id::new(cl, pc, i);
                    assert_eq!(Ok(i), id.number());
                }
                // i16
                for i in 0..=i16::MAX {
                    let id = Id::new(cl, pc, i as u16);
                    assert_eq!(Ok(i), id.number());
                }
                // u16
                for i in 0..=u16::MAX {
                    let id = Id::new(cl, pc, i);
                    assert_eq!(Ok(i), id.number());
                }
                // u128::MAX
                {
                    let id = Id::new(cl, pc, u128::MAX);
                    assert_eq!(Ok(u128::MAX), id.number());
                }
            }
        }
    }

    #[test]
    fn number_overflow() {
        for &cl in CLASSES {
            for &pc in PCS {
                // i8
                {
                    let id = Id::new(cl, pc, i8::MAX as u128 + 1);
                    assert!(id.number::<i8>().is_err());
                }
                // u8
                {
                    let id = Id::new(cl, pc, u8::MAX as u128 + 1);
                    assert!(id.number::<u8>().is_err());
                }
                // i16
                {
                    let id = Id::new(cl, pc, i16::MAX as u128 + 1);
                    assert!(id.number::<i16>().is_err());
                }
                // u16
                {
                    let id = Id::new(cl, pc, u16::MAX as u128 + 1);
                    assert!(id.number::<u16>().is_err());
                }
                // i128
                {
                    let id = Id::new(cl, pc, i128::MAX as u128 + 1);
                    assert!(id.number::<i128>().is_err());
                }
                // u128
                {
                    let mut bytes = [0x80; 20];
                    bytes[0] = cl as u8 | pc as u8 | LONG_FLAG;
                    bytes[1] = 0x84;
                    bytes[19] = 0x00;
                    let id = Id::parse(&bytes as &[u8]).unwrap();
                    assert!(id.number::<u128>().is_err());
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
                    let idref = IdRef::parse(id.as_ref()).unwrap();
                    assert_eq!(idref, &id);
                }
            }
        }
    }

    #[test]
    fn id_new_u8() {
        for &cl in CLASSES {
            for &pc in PCS {
                for i in 0..=MAX_SHORT {
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + i];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
                for i in (MAX_SHORT + 1)..0x80 {
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, i];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
                for i in 0x80..=u8::MAX {
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, 0x81, i - 0x80];
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
                    for i in 0..=MAX_SHORT {
                        let id = Id::new(cl, pc, i as u16);
                        let expected: &[u8] = &[cl as u8 + pc as u8 + i];
                        assert_eq!(id.as_ref() as &[u8], expected);
                    }
                    for i in (MAX_SHORT + 1)..0x80 {
                        let id = Id::new(cl, pc, i as u16);
                        let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, i];
                        assert_eq!(id.as_ref() as &[u8], expected);
                    }
                    for i in 0x80..=u8::MAX {
                        let id = Id::new(cl, pc, i as u16);
                        let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, 0x81, i - 0x80];
                        assert_eq!(id.as_ref() as &[u8], expected);
                    }
                }

                // u8::MAX + 1
                {
                    let i = u8::MAX as u16 + 1;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, 0x82, 0];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // i16::MAX
                {
                    let i = i16::MAX as u16;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, 0x81, 0xff, 0x7f];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // i16::MAX + 1
                {
                    let i = i16::MAX as u16 + 1;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, 0x82, 0x80, 0x00];
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // u16::MAX
                {
                    let i = u16::MAX;
                    let id = Id::new(cl, pc, i);
                    let expected: &[u8] = &[cl as u8 + pc as u8 + LONG_FLAG, 0x83, 0xff, 0x7f];
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
                    expected[0] = cl as u8 + pc as u8 + LONG_FLAG;
                    expected[1] = 0x81;
                    expected[10] = 0x7f;
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // u64::MAX + 1
                {
                    let i = u64::MAX as u128 + 1;
                    let id = Id::new(cl, pc, i);
                    let expected: &mut [u8] = &mut [0x80; 11];
                    expected[0] = cl as u8 + pc as u8 + LONG_FLAG;
                    expected[1] = 0x82;
                    expected[10] = 0x00;
                    assert_eq!(id.as_ref() as &[u8], expected);
                }

                // u128::MAX
                {
                    let i = u128::MAX;
                    let id = Id::new(cl, pc, i);
                    let expected: &mut [u8] = &mut [0xff; 20];
                    expected[0] = cl as u8 + pc as u8 + LONG_FLAG;
                    expected[1] = 0x83;
                    expected[19] = 0x7f;
                    assert_eq!(id.as_ref() as &[u8], expected);
                }
            }
        }
    }

    #[test]
    fn set_number() {
        for &cl in CLASSES {
            for &pc in PCS {
                let mut id = Id::new(cl, pc, 0_u8);

                for i in 0..=u16::MAX {
                    id.set_number(i);
                    assert_eq!(cl, id.class());
                    assert_eq!(pc, id.pc());
                    assert_eq!(Ok(i), id.number());
                }

                for i in (0..=u16::MAX).rev() {
                    id.set_number(i);
                    assert_eq!(cl, id.class());
                    assert_eq!(pc, id.pc());
                    assert_eq!(Ok(i), id.number());
                }
            }
        }
    }
}
