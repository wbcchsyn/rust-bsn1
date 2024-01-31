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

//! Provides trait `Serialize`.

use bsn1::{Contents, ContentsRef, Error, IdRef, Length};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, LinkedList, VecDeque};
use std::io::Write;

/// A **data structure** that can be serialized into ASN.1 format.
pub trait Serialize {
    /// Writes the `ID` of ASN.1 format into `buffer` .
    ///
    /// # Warnings
    ///
    /// It depends on the implementation whether `buffer.flush()` is called or not.
    /// Users should call `buffer.flush()` explicitly if necessary.
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error>;

    /// Serializes `self` into contents of ASN.1 DER format and writes it into `buffer` .
    ///
    /// # Warnings
    ///
    /// It depends on the implementation whether `buffer.flush()` is called or not.
    /// Users should call `buffer.flush()` explicitly if necessary.
    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error>;

    /// Returns the byte count of the identifier of ASN.1 format.
    fn id_len(&self) -> Result<usize, Error>;

    /// Returns the byte count of the contents of ASN.1 DER format.
    fn der_contents_len(&self) -> Result<usize, Error>;
}

impl Serialize for bool {
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::boolean().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::integer().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
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
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::utf8_string().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer.write_all(self.as_bytes()).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        Ok(self.len())
    }
}

impl<T> Serialize for Vec<T>
where
    T: Serialize,
{
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::sequence().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        for t in self.iter() {
            write_der(t, buffer)?;
        }

        Ok(())
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let mut ret = 0;
        for t in self.iter() {
            ret += der_len(t)?;
        }
        Ok(ret)
    }
}

impl<T> Serialize for LinkedList<T>
where
    T: Serialize,
{
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::sequence().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        for t in self.iter() {
            write_der(t, buffer)?;
        }
        Ok(())
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let mut ret = 0;
        for t in self.iter() {
            ret += der_len(t)?;
        }
        Ok(ret)
    }
}

impl<T> Serialize for VecDeque<T>
where
    T: Serialize,
{
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::sequence().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        for t in self.iter() {
            write_der(t, buffer)?;
        }
        Ok(())
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let mut ret = 0;
        for t in self.iter() {
            ret += der_len(t)?;
        }
        Ok(ret)
    }
}

impl<T> Serialize for BTreeSet<T>
where
    T: Serialize,
{
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::sequence().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        for t in self.iter() {
            write_der(t, buffer)?;
        }
        Ok(())
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let mut ret = 0;
        for t in self.iter() {
            ret += der_len(t)?;
        }
        Ok(ret)
    }
}

impl<K, V> Serialize for BTreeMap<K, V>
where
    K: Serialize,
    V: Serialize,
{
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer
            .write_all(IdRef::sequence().as_ref())
            .map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        for (k, v) in self.iter() {
            let length = Length::Definite(der_len(k)? + der_len(v)?);

            buffer.write_all(IdRef::sequence().as_ref())?;
            buffer.write_all(length.to_bytes().as_ref())?;
            write_der(k, buffer)?;
            write_der(v, buffer)?;
        }
        Ok(())
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let mut ret = 0;
        for (k, v) in self.iter() {
            let content_len = der_len(k)? + der_len(v)?;
            let length = Length::Definite(content_len);
            ret += IdRef::sequence().len() + length.len() + content_len;
        }
        Ok(ret)
    }
}

impl<T> Serialize for HashSet<T>
where
    T: Serialize,
{
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer.write_all(IdRef::set().as_ref()).map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        for t in self.iter() {
            write_der(t, buffer)?;
        }
        Ok(())
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let mut ret = 0;
        for t in self.iter() {
            ret += der_len(t)?;
        }
        Ok(ret)
    }
}

impl<K, V> Serialize for HashMap<K, V>
where
    K: Serialize,
    V: Serialize,
{
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer.write_all(IdRef::set().as_ref()).map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        for (k, v) in self.iter() {
            let length = Length::Definite(der_len(k)? + der_len(v)?);

            buffer.write_all(IdRef::sequence().as_ref())?;
            buffer.write_all(length.to_bytes().as_ref())?;
            write_der(k, buffer)?;
            write_der(v, buffer)?;
        }

        Ok(())
    }

    fn id_len(&self) -> Result<usize, Error> {
        Ok(1)
    }

    fn der_contents_len(&self) -> Result<usize, Error> {
        let mut ret = 0;
        for (k, v) in self.iter() {
            let content_len = der_len(k)? + der_len(v)?;
            let length = Length::Definite(content_len);
            ret += IdRef::sequence().len() + length.len() + content_len;
        }
        Ok(ret)
    }
}

fn der_len<T: Serialize>(t: &T) -> Result<usize, Error> {
    let id_len = t.id_len()?;
    let contents_len = t.der_contents_len()?;
    Ok(id_len + Length::Definite(contents_len).len() + contents_len)
}

fn write_der<T: Serialize, W: ?Sized + Write>(t: &T, buffer: &mut W) -> Result<(), Error> {
    t.write_id(buffer)?;

    let contents_len = t.der_contents_len()?;
    let length = Length::Definite(contents_len).to_bytes();
    buffer.write_all(&length).unwrap(); // Buffer::write_all() never fails.
    t.write_der_contents(buffer)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use bsn1::{Der, DerRef};

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

    #[test]
    fn vec_to_der() {
        for i in 0..100 {
            let v: Vec<i32> = (0..i).collect();
            let der = crate::to_der(&v).unwrap();

            assert_eq!(der.id(), IdRef::sequence());
            assert_eq!(der.id().len(), v.id_len().unwrap());

            assert_eq!(
                der.length().definite().unwrap(),
                v.der_contents_len().unwrap()
            );

            let mut contents: &[u8] = der.contents().as_ref();
            assert_eq!(contents.len(), v.der_contents_len().unwrap());

            for &i in v.iter() {
                let der = DerRef::parse(&mut contents).unwrap();

                assert_eq!(der.id(), IdRef::integer());
                assert_eq!(der.contents(), &Contents::from(i));
            }

            assert_eq!(contents.is_empty(), true);
        }
    }

    #[test]
    fn linked_list_to_der() {
        let v: LinkedList<String> = LinkedList::new();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());
        assert_eq!(der.contents().is_empty(), true);

        let v: LinkedList<i8> = (i8::MIN..=i8::MAX).collect();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());

        let mut contents: &[u8] = der.contents().as_ref();
        for &i in v.iter() {
            let der = DerRef::parse(&mut contents).unwrap();
            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.contents(), &Contents::from(i));
        }
        assert_eq!(contents.is_empty(), true);
    }

    #[test]
    fn vec_deque_to_der() {
        let v: VecDeque<String> = VecDeque::new();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());
        assert_eq!(der.contents().is_empty(), true);

        let v: VecDeque<i8> = (i8::MIN..=i8::MAX).collect();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());

        let mut contents: &[u8] = der.contents().as_ref();
        for &i in v.iter() {
            let der = DerRef::parse(&mut contents).unwrap();
            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.contents(), &Contents::from(i));
        }
        assert_eq!(contents.is_empty(), true);
    }

    #[test]
    fn btree_set_to_der() {
        let v: BTreeSet<String> = BTreeSet::new();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());
        assert_eq!(der.contents().is_empty(), true);

        let v: BTreeSet<i8> = (i8::MIN..=i8::MAX).collect();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());

        let mut contents: &[u8] = der.contents().as_ref();
        for &i in v.iter() {
            let der = DerRef::parse(&mut contents).unwrap();
            assert_eq!(der.id(), IdRef::integer());
            assert_eq!(der.contents(), &Contents::from(i));
        }
        assert_eq!(contents.is_empty(), true);
    }

    #[test]
    fn btree_map_to_der() {
        let v: BTreeMap<i32, String> = BTreeMap::new();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());
        assert_eq!(der.contents().is_empty(), true);

        let v: BTreeMap<i8, String> = (i8::MIN..=i8::MAX).map(|i| (i, i.to_string())).collect();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::sequence());

        let mut contents: &[u8] = der.contents().as_ref();
        for (k, v) in v.iter() {
            let der1 = DerRef::parse(&mut contents).unwrap();
            assert_eq!(der1.id(), IdRef::sequence());

            let mut contents1: &[u8] = der1.contents().as_ref();
            let der2 = DerRef::parse(&mut contents1).unwrap();
            let der3 = DerRef::parse(&mut contents1).unwrap();
            assert_eq!(contents1.is_empty(), true);

            assert_eq!(der2.id(), IdRef::integer());
            assert_eq!(der2.contents(), &Contents::from(*k));
            assert_eq!(der3.id(), IdRef::utf8_string());
            assert_eq!(der3.contents(), &Contents::from(v.as_bytes()));
        }
        assert_eq!(contents.is_empty(), true);
    }

    #[test]
    fn hash_set_to_der() {
        let v: HashSet<String> = HashSet::new();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::set());
        assert_eq!(der.contents().is_empty(), true);

        let mut v: HashSet<i8> = (i8::MIN..=i8::MAX).collect();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::set());

        let mut contents: &[u8] = der.contents().as_ref();
        while 0 < contents.len() {
            let der = DerRef::parse(&mut contents).unwrap();
            assert_eq!(der.id(), IdRef::integer());

            let i: i8 = der.contents().to_integer().unwrap();
            assert_eq!(v.remove(&i), true);
        }
        assert_eq!(v.is_empty(), true);
    }

    #[test]
    fn hash_map_to_der() {
        let v: HashMap<i32, String> = HashMap::new();
        let der = crate::to_der(&v).unwrap();
        assert_eq!(der.id(), IdRef::set());
        assert_eq!(der.contents().is_empty(), true);

        let mut vals: HashMap<i8, String> =
            (i8::MIN..=i8::MAX).map(|i| (i, i.to_string())).collect();
        let der = crate::to_der(&vals).unwrap();
        assert_eq!(der.id(), IdRef::set());

        let mut contents: &[u8] = der.contents().as_ref();
        while 0 < contents.len() {
            let der1 = DerRef::parse(&mut contents).unwrap();
            assert_eq!(der1.id(), IdRef::sequence());

            let mut contents1: &[u8] = der1.contents().as_ref();
            let der2 = DerRef::parse(&mut contents1).unwrap();
            let der3 = DerRef::parse(&mut contents1).unwrap();
            assert_eq!(contents1.is_empty(), true);

            assert_eq!(der2.id(), IdRef::integer());
            let k: i8 = der2.contents().to_integer().unwrap();

            assert_eq!(der3.id(), IdRef::utf8_string());
            let v = String::from_utf8(der3.contents().as_ref().into()).unwrap();

            assert_eq!(vals.remove(&k), Some(v));
        }
        assert_eq!(vals.is_empty(), true);
    }
}
