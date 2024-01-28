// Copyright 2023-2024 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of bsn1_serde
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

//! Provides trait `Deserialize`.

use bsn1::{BerRef, ContentsRef, DerRef, Error, IdRef, Length};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, LinkedList, VecDeque};
use std::hash::Hash;

/// A **data structure** that can be deserialized from ASN.1 DER format.
pub trait Deserialize: Sized {
    /// Deserializes `Self` from ASN.1 BER format.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `length` is invalid.
    ///
    /// ex)
    /// - `length` is indefinite where only definite length is allowed.
    /// - `length` is definite but the value does not match the length of `contents`.
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error>;

    /// Deserializes `Self` from ASN.1 DER format.
    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error>;
}

impl Deserialize for bool {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::boolean() {
            Err(Error::UnmatchedId)
        } else if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            contents.to_bool_ber()
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::boolean() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_bool_der()
        }
    }
}

impl Deserialize for i8 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for u8 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for i16 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for u16 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for i32 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for u32 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for i64 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for u64 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for i128 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for u128 {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for isize {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for usize {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            Self::from_der(id, contents)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::integer() {
            Err(Error::UnmatchedId)
        } else {
            contents.to_integer()
        }
    }
}

impl Deserialize for String {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::utf8_string() && id != IdRef::utf8_string_constructed() {
            Err(Error::UnmatchedId)
        } else if length == Length::Indefinite {
            Err(Error::IndefiniteLength)
        } else {
            debug_assert_eq!(length.definite(), Some(contents.len()));
            match std::str::from_utf8(contents.as_ref()) {
                Ok(s) => Ok(s.into()),
                Err(_) => Err(Error::InvalidUtf8),
            }
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::utf8_string() {
            Err(Error::UnmatchedId)
        } else {
            match std::str::from_utf8(contents.as_ref()) {
                Ok(s) => Ok(s.into()),
                Err(_) => Err(Error::InvalidUtf8),
            }
        }
    }
}

impl<T> Deserialize for Vec<T>
where
    T: Deserialize,
{
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut contents: &[u8] = exclude_eoc(length, contents).map(AsRef::as_ref)?;
            let mut ret = Vec::new();

            while !contents.is_empty() {
                let ber = BerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_ber(ber.id(), ber.length(), ber.contents())?;
                ret.push(t);
            }

            Ok(ret)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut ret = Vec::new();
            let mut contents: &[u8] = contents.as_ref();

            while !contents.is_empty() {
                let der = DerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_der(der.id(), der.contents())?;
                ret.push(t);
            }

            Ok(ret)
        }
    }
}

impl<T> Deserialize for LinkedList<T>
where
    T: Deserialize,
{
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut contents: &[u8] = exclude_eoc(length, contents).map(AsRef::as_ref)?;
            let mut ret = LinkedList::new();

            while !contents.is_empty() {
                let ber = BerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_ber(ber.id(), ber.length(), ber.contents())?;
                ret.push_back(t);
            }

            Ok(ret)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut ret = LinkedList::new();
            let mut contents: &[u8] = contents.as_ref();

            while !contents.is_empty() {
                let der = DerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_der(der.id(), der.contents())?;
                ret.push_back(t);
            }

            Ok(ret)
        }
    }
}

impl<T> Deserialize for VecDeque<T>
where
    T: Deserialize,
{
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut contents: &[u8] = exclude_eoc(length, contents).map(AsRef::as_ref)?;
            let mut ret = VecDeque::new();

            while !contents.is_empty() {
                let ber = BerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_ber(ber.id(), ber.length(), ber.contents())?;
                ret.push_back(t);
            }

            Ok(ret)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut ret = VecDeque::new();
            let mut contents: &[u8] = contents.as_ref();

            while !contents.is_empty() {
                let der = DerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_der(der.id(), der.contents())?;
                ret.push_back(t);
            }

            Ok(ret)
        }
    }
}

impl<T> Deserialize for BTreeSet<T>
where
    T: Deserialize + Ord,
{
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut contents: &[u8] = exclude_eoc(length, contents).map(AsRef::as_ref)?;
            let mut ret = BTreeSet::new();

            while !contents.is_empty() {
                let ber = BerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_ber(ber.id(), ber.length(), ber.contents())?;
                ret.insert(t);
            }

            Ok(ret)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut ret = BTreeSet::new();
            let mut contents: &[u8] = contents.as_ref();

            while !contents.is_empty() {
                let der = DerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_der(der.id(), der.contents())?;
                ret.insert(t);
            }

            Ok(ret)
        }
    }
}

impl<K, V> Deserialize for BTreeMap<K, V>
where
    K: Deserialize + Ord,
    V: Deserialize,
{
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut contents: &[u8] = exclude_eoc(length, contents).map(AsRef::as_ref)?;
            let mut ret = BTreeMap::new();

            while !contents.is_empty() {
                let pair = BerRef::parse(&mut contents)?;

                if pair.id() != IdRef::sequence() {
                    return Err(Error::UnmatchedId);
                }

                let mut pair_contents: &[u8] = pair.contents().as_ref();
                let key = BerRef::parse(&mut pair_contents)?;
                let val = BerRef::parse(&mut pair_contents)?;
                if pair_contents.is_empty() {
                    let key = Deserialize::from_ber(key.id(), key.length(), key.contents())?;
                    let val = Deserialize::from_ber(val.id(), val.length(), val.contents())?;
                    ret.insert(key, val);
                }
            }

            Ok(ret)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::sequence() {
            Err(Error::UnmatchedId)
        } else {
            let mut ret = BTreeMap::new();
            let mut contents: &[u8] = contents.as_ref();

            while !contents.is_empty() {
                let pair = DerRef::parse(&mut contents)?;

                if pair.id() != IdRef::sequence() {
                    return Err(Error::UnmatchedId);
                }

                let mut pair_contents: &[u8] = pair.contents().as_ref();
                let key = DerRef::parse(&mut pair_contents)?;
                let val = DerRef::parse(&mut pair_contents)?;
                if pair_contents.is_empty() {
                    let key = Deserialize::from_der(key.id(), key.contents())?;
                    let val = Deserialize::from_der(val.id(), val.contents())?;
                    ret.insert(key, val);
                }
            }

            Ok(ret)
        }
    }
}

impl<T> Deserialize for HashSet<T>
where
    T: Deserialize + Eq + Hash,
{
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::set() {
            Err(Error::UnmatchedId)
        } else {
            let mut contents: &[u8] = exclude_eoc(length, contents).map(AsRef::as_ref)?;
            let mut ret = HashSet::new();

            while !contents.is_empty() {
                let ber = BerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_ber(ber.id(), ber.length(), ber.contents())?;
                ret.insert(t);
            }

            Ok(ret)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::set() {
            Err(Error::UnmatchedId)
        } else {
            let mut ret = HashSet::new();
            let mut contents: &[u8] = contents.as_ref();

            while !contents.is_empty() {
                let der = DerRef::parse(&mut contents)?;
                let t: T = Deserialize::from_der(der.id(), der.contents())?;
                ret.insert(t);
            }

            Ok(ret)
        }
    }
}

impl<K, V> Deserialize for HashMap<K, V>
where
    K: Deserialize + std::hash::Hash + Eq,
    V: Deserialize,
{
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::set() {
            Err(Error::UnmatchedId)
        } else {
            let mut contents: &[u8] = exclude_eoc(length, contents).map(AsRef::as_ref)?;
            let mut ret = HashMap::new();

            while !contents.is_empty() {
                let pair = BerRef::parse(&mut contents)?;

                if pair.id() != IdRef::sequence() {
                    return Err(Error::UnmatchedId);
                }

                let mut pair_contents: &[u8] = pair.contents().as_ref();
                let key = BerRef::parse(&mut pair_contents)?;
                let val = BerRef::parse(&mut pair_contents)?;
                if pair_contents.is_empty() {
                    let key = Deserialize::from_ber(key.id(), key.length(), key.contents())?;
                    let val = Deserialize::from_ber(val.id(), val.length(), val.contents())?;
                    ret.insert(key, val);
                }
            }

            Ok(ret)
        }
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        if id != IdRef::set() {
            Err(Error::UnmatchedId)
        } else {
            let mut ret = HashMap::new();
            let mut contents: &[u8] = contents.as_ref();

            while !contents.is_empty() {
                let pair = DerRef::parse(&mut contents)?;

                if pair.id() != IdRef::sequence() {
                    return Err(Error::UnmatchedId);
                }

                let mut pair_contents: &[u8] = pair.contents().as_ref();
                let key = DerRef::parse(&mut pair_contents)?;
                let val = DerRef::parse(&mut pair_contents)?;
                if pair_contents.is_empty() {
                    let key = Deserialize::from_der(key.id(), key.contents())?;
                    let val = Deserialize::from_der(val.id(), val.contents())?;
                    ret.insert(key, val);
                }
            }

            Ok(ret)
        }
    }
}

fn exclude_eoc(length: Length, contents: &ContentsRef) -> Result<&ContentsRef, Error> {
    match length {
        Length::Definite(len) => {
            debug_assert_eq!(len, contents.len());
            Ok(contents)
        }
        Length::Indefinite => {
            let eoc = BerRef::eoc();
            let contents: &[u8] = contents.as_ref();

            if contents.ends_with(eoc.as_ref()) {
                let contents = &contents[..contents.len() - eoc.as_ref().len()];
                Ok(contents.into())
            } else {
                Err(Error::UnTerminatedBytes)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{to_ber, to_der};

    #[test]
    fn boolean() {
        for b in [false, true] {
            let ber = to_ber(&b).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(b));

            let der = to_der(&b).unwrap();
            assert_eq!(crate::from_der(&der), Ok(b));
        }
    }

    #[test]
    fn i8() {
        for i in i8::MIN..=i8::MAX {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn u8() {
        for i in u8::MIN..=u8::MAX {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn i16() {
        for i in i16::MIN..=i16::MAX {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn u16() {
        for i in u16::MIN..=u16::MAX {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn i32() {
        for i in [i32::MIN, 0, i32::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn u32() {
        for i in [u32::MIN, u32::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn i64() {
        for i in [i64::MIN, 0, i64::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn u64() {
        for i in [u64::MIN, u64::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn i128() {
        for i in [i128::MIN, 0, i128::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn u128() {
        for i in [u128::MIN, u128::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn isize() {
        for i in [isize::MIN, 0, isize::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn usize() {
        for i in [usize::MIN, usize::MAX] {
            let ber = to_ber(&i).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(i));

            let der = to_der(&i).unwrap();
            assert_eq!(crate::from_der(&der), Ok(i));
        }
    }

    #[test]
    fn string() {
        for s in ["", "a", "abc", "あいうえお"] {
            let s = s.to_string();

            let ber = to_ber(&s).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(s.to_string()));

            let der = to_der(&s).unwrap();
            assert_eq!(crate::from_der(&der), Ok(s.to_string()));
        }
    }

    #[test]
    fn vec() {
        for v in [vec![-1, 0, 1], vec![1], vec![]] {
            let ber = to_ber(&v).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(v.clone()));

            let der = to_der(&v).unwrap();
            assert_eq!(crate::from_der(&der), Ok(v.clone()));
        }
    }

    #[test]
    fn linked_list() {
        for v in [vec![-1, 0, 1], vec![1], vec![]] {
            let l = LinkedList::from_iter(v.into_iter());
            let ber = to_ber(&l).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(l.clone()));

            let der = to_der(&l).unwrap();
            assert_eq!(crate::from_der(&der), Ok(l.clone()));
        }
    }

    #[test]
    fn vec_deque() {
        for v in [vec![-1, 0, 1], vec![1], vec![]] {
            let q = VecDeque::from_iter(v.into_iter());
            let ber = to_ber(&q).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(q.clone()));

            let der = to_der(&q).unwrap();
            assert_eq!(crate::from_der(&der), Ok(q.clone()));
        }
    }

    #[test]
    fn btree_set() {
        let vals = -10..10;

        for i in 0..vals.clone().count() {
            let s = BTreeSet::from_iter(vals.clone().take(i));

            let ber = to_ber(&s).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(s.clone()));

            let der = to_der(&s).unwrap();
            assert_eq!(crate::from_der(&der), Ok(s.clone()));
        }
    }

    #[test]
    fn btree_map() {
        let keys = -10..10;
        let vals = 100..;

        for i in 0..keys.clone().count() {
            let mut val = BTreeMap::new();
            for (k, v) in keys.clone().zip(vals.clone()).take(i) {
                val.insert(k, v);
            }

            let ber = to_ber(&val).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(val.clone()));

            let der = to_der(&val).unwrap();
            assert_eq!(crate::from_der(&der), Ok(val.clone()));
        }
    }

    #[test]
    fn hash_set() {
        let vals = -10..10;

        for i in 0..vals.clone().count() {
            let s = HashSet::from_iter(vals.clone().take(i));

            let ber = to_ber(&s).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(s.clone()));

            let der = to_der(&s).unwrap();
            assert_eq!(crate::from_der(&der), Ok(s.clone()));
        }
    }

    #[test]
    fn hash_map() {
        let keys = -10..10;
        let vals = 100..;

        for i in 0..keys.clone().count() {
            let mut val = HashMap::new();
            for (k, v) in keys.clone().zip(vals.clone()).take(i) {
                val.insert(k, v);
            }

            let ber = to_ber(&val).unwrap();
            assert_eq!(crate::from_ber(&ber), Ok(val.clone()));

            let der = to_der(&val).unwrap();
            assert_eq!(crate::from_der(&der), Ok(val.clone()));
        }
    }
}
