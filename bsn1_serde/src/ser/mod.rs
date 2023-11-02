// Copyright 2023 Shin Yoshida
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

//! Provides trait `Serialize`.

use bsn1::{Contents, ContentsRef, Error, IdRef};
use std::io::Write;

/// A **data structure** that can be serialized into ASN.1 format.
pub trait Serialize {
    /// Writes the `ID` of ASN.1 format into `buffer` .
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error>;

    /// Serializes `self` into contents of ASN.1 DER format and writes it into `buffer` .
    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error>;

    /// Returns the byte count of the identifier of ASN.1 format.
    fn id_len(&self) -> Result<usize, Error>;

    /// Returns the byte count of the contents of ASN.1 DER format.
    fn der_contents_len(&self) -> Result<usize, Error>;
}

impl Serialize for bool {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::boolean().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(<&ContentsRef>::from(*self).as_ref())
            .map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        Ok(1)
    }
}

impl Serialize for i8 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        Ok(1)
    }
}

impl Serialize for u8 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        if *self <= (i8::MAX as u8) {
            Ok(1)
        } else {
            Ok(2)
        }
    }
}

impl Serialize for i16 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        if (i8::MIN as i16) <= *self && *self <= (i8::MAX as i16) {
            Ok(1)
        } else {
            Ok(2)
        }
    }
}

impl Serialize for u16 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        if *self <= (i8::MAX as u16) {
            Ok(1)
        } else if *self <= (i16::MAX as u16) {
            Ok(2)
        } else {
            Ok(3)
        }
    }
}

impl Serialize for i32 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = if self.is_negative() {
            (Self::BITS + u8::BITS - self.leading_ones()) / u8::BITS
        } else {
            (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS
        };

        Ok(ret as usize)
    }
}

impl Serialize for u32 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS;
        Ok(ret as usize)
    }
}

impl Serialize for i64 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = if self.is_negative() {
            (Self::BITS + u8::BITS - self.leading_ones()) / u8::BITS
        } else {
            (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS
        };

        Ok(ret as usize)
    }
}

impl Serialize for u64 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS;
        Ok(ret as usize)
    }
}

impl Serialize for i128 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = if self.is_negative() {
            (Self::BITS + u8::BITS - self.leading_ones()) / u8::BITS
        } else {
            (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS
        };

        Ok(ret as usize)
    }
}

impl Serialize for u128 {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS;
        Ok(ret as usize)
    }
}

impl Serialize for isize {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = if self.is_negative() {
            (Self::BITS + u8::BITS - self.leading_ones()) / u8::BITS
        } else {
            (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS
        };

        Ok(ret as usize)
    }
}

impl Serialize for usize {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        let contents = Contents::from(*self);
        buffer.write_all(contents.as_ref()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let ret = (Self::BITS + u8::BITS - self.leading_zeros()) / u8::BITS;
        Ok(ret as usize)
    }
}

impl Serialize for String {
    fn write_id<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::utf8_string().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer.write_all(self.as_bytes()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        Ok(self.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bsn1::Der;

    #[test]
    fn bool_to_der() {
        for val in [true, false].iter() {
            let der = crate::to_der(val).unwrap();

            assert_eq!(der, Der::from(*val));
            assert_eq!(der.id().len(), val.id_len().unwrap());
            assert_eq!(der.contents().len(), val.der_contents_len().unwrap());
        }
    }

    #[test]
    fn i8_to_der() {
        for i in i8::MIN..=i8::MAX {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn u8_to_der() {
        for i in u8::MIN..=u8::MAX {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn i16_to_der() {
        for i in i16::MIN..=i16::MAX {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn u16_to_der() {
        for i in u16::MIN..=u16::MAX {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn i32_to_der() {
        for i in [i32::MIN, 0, i32::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn u32_to_der() {
        for i in [u32::MIN, u32::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn i64_to_der() {
        for i in [i64::MIN, 0, i64::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn u64_to_der() {
        for i in [u64::MIN, u64::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn i128_to_der() {
        for i in [i128::MIN, 0, i128::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn u128_to_der() {
        for i in [u128::MIN, u128::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn isize_to_der() {
        for i in [isize::MIN, 0, isize::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn usize_to_der() {
        for i in [usize::MIN, usize::MAX] {
            let der = crate::to_der(&i).unwrap();

            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.id().len(), i.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                i.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(i));
            assert_eq!(der.contents().len(), i.der_contents_len().unwrap());
        }
    }

    #[test]
    fn string_to_der() {
        for s in [
            "".to_string(),
            "a".to_string(),
            "abc".to_string(),
            "あいうえお".to_string(),
        ] {
            let der = crate::to_der(&s).unwrap();

            assert_eq!(der.id(), IdRef::utf8_string());
            assert_eq!(der.id().len(), s.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                s.der_contents_len().unwrap()
            );

            assert_eq!(der.contents(), &Contents::from(s.as_bytes()));
            assert_eq!(der.contents().len(), s.der_contents_len().unwrap());
        }
    }
}
