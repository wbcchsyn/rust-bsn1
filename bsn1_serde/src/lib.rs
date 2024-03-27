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

#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

pub mod de;
#[doc(hidden)]
pub mod macro_alias;
mod octet_string;
pub mod ser;

use bsn1::{Ber, BerRef, Buffer, Der, DerRef, Error, Length};
pub use bsn1_serde_macros::{Deserialize, Serialize};
pub use octet_string::OctetString;
use std::io::{Read, Write};

/// Serializes `value` into ASN.1 DER format.
pub fn to_der<T>(value: &T) -> Result<Der, Error>
where
    T: ?Sized + ser::Serialize,
{
    let (contents_len, contents) = match value.der_contents_len()? {
        Some(len) => (len, None),
        None => {
            let mut contents = Buffer::new();
            value.write_der_contents(&mut contents)?;
            (contents.len(), Some(contents))
        }
    };

    let length = Length::Definite(contents_len).to_bytes();
    let mut buffer = Buffer::new();

    if let Some(id_len) = value.id_len()? {
        let der_len = id_len + length.len() + contents_len;
        buffer.reserve(der_len);
    }

    value.write_id(&mut buffer)?;
    buffer.write_all(&length).unwrap(); // Buffer::write_all() never fails.

    if let Some(contents) = contents {
        buffer.write_all(&contents.as_slice()).unwrap(); // Buffer::write_all() never fails.
    } else {
        value.write_der_contents(&mut buffer)?;
    }

    Ok(buffer.into())
}

/// Serializes `value` into ASN.1 BER format.
pub fn to_ber<T>(value: &T) -> Result<Ber, Error>
where
    T: ?Sized + ser::Serialize,
{
    // DER is always valid as BER.
    to_der(value).map(Ber::from)
}

/// Serializes `value` into ASN.1 DER format, and writes it into `write`.
///
/// # Warnings
///
/// It depends on the implementation whether `write.flush()` is called or not.
/// Users should call `write.flush()` explicitly if necessary.
pub fn write_der<T, W>(value: &T, write: &mut W) -> Result<(), Error>
where
    T: ?Sized + ser::Serialize,
    W: ?Sized + Write,
{
    let (contents_len, contents) = match value.der_contents_len()? {
        Some(len) => (len, None),
        None => {
            let mut contents = Buffer::new();
            value.write_der_contents(&mut contents)?;
            (contents.len(), Some(contents))
        }
    };

    let length = Length::Definite(contents_len).to_bytes();

    value.write_id(write)?;
    write.write_all(&length).map_err(Error::from)?;

    if let Some(contents) = contents {
        write.write_all(contents.as_slice())?;
    } else {
        value.write_der_contents(write)?;
    }

    Ok(())
}

/// Serializes `value` into ASN.1 BER format, and writes it into `write`.
///
/// # Warnings
///
/// It depends on the implementation whether `write.flush()` is called or not.
/// Users should call `write.flush()` explicitly if necessary.
pub fn write_ber<T, W>(value: &T, write: &mut W) -> Result<(), Error>
where
    T: ?Sized + ser::Serialize,
    W: ?Sized + Write,
{
    // DER is always valid as BER.
    write_der(value, write)
}

/// Deserializes `T` from ASN.1 BER format.
pub fn from_ber<T>(ber: &BerRef) -> Result<T, Error>
where
    T: de::Deserialize,
{
    let (id, length, contents) = ber.disassemble();
    unsafe { de::Deserialize::from_ber(id, length, contents) }
}

/// Deserializes `T` from ASN.1 DER format.
pub fn from_der<T>(der: &DerRef) -> Result<T, Error>
where
    T: de::Deserialize,
{
    let (id, _, contents) = der.disassemble();
    de::Deserialize::from_der(id, contents)
}

/// Parses ASN.1 BER format from `buffer`, and deserializes `T` from it.
///
/// The state of `read` is unspecified on failure to parse BER; otherwise,
/// `read` is advanced to the end of the BER (even if this function fails to deserialize `T`.)
///
/// The result of this function is same to [`read_ber`], however, this function is more efficient
/// if `buffer` is `&mut &[u8]`.
pub fn parse_ber<T>(buffer: &mut &[u8]) -> Result<T, Error>
where
    T: de::Deserialize,
{
    let ber = BerRef::parse(buffer)?;
    from_ber(&ber)
}

/// Parses ASN.1 DER format from `buffer`, and deserializes `T` from it.
///
/// The state of `read` is unspecified on failure to parse DER; otherwise,
/// `read` is advanced to the end of the DER (even if this function fails to deserialize `T`.)
///
/// The result of this function is same to [`read_der`], however, this function is more efficient
/// if `buffer` is `&mut &[u8]`.
pub fn parse_der<T>(buffer: &mut &[u8]) -> Result<T, Error>
where
    T: de::Deserialize,
{
    let der = DerRef::parse(buffer)?;
    from_der(&der)
}

/// Parses ASN.1 BER format from `read`, and deserializes `T` from it.
///
/// The state of `read` is unspecified on failure to parse BER; otherwise,
/// `read` is advanced to the end of the BER (even if this function fails to deserialize `T`.)
///
/// Note that if `R` is `&[u8]`, [`parse_ber`] is more efficient.
pub fn read_ber<R, T>(read: &mut R) -> Result<T, Error>
where
    R: ?Sized + Read,
    T: de::Deserialize,
{
    let ber = Ber::parse(read)?;
    from_ber(&ber)
}

/// Parses ASN.1 DER format from `read`, and deserializes `T` from it.
///
/// The state of `read` is unspecified on failure to parse DER; otherwise,
/// `read` is advanced to the end of the DER (even if this function fails to deserialize `T`.)
///
/// Note that if `R` is `&[u8]`, [`parse_der`] is more efficient.
pub fn read_der<R, T>(read: &mut R) -> Result<T, Error>
where
    R: ?Sized + Read,
    T: de::Deserialize,
{
    let der = Der::parse(read)?;
    from_der(&der)
}

#[cfg(test)]
mod tests {
    use self::ser::Serialize;

    use super::*;
    use bsn1::{Contents, IdRef};

    #[test]
    fn test_to_der() {
        let value = 0x1234u16;
        let der = to_der(&value).unwrap();

        assert_eq!(der.id(), IdRef::integer());
        assert_eq!(der.contents(), &Contents::from(value));
    }

    #[test]
    fn test_to_ber() {
        let value = "abc".to_string();
        let ber = to_ber(&value).unwrap();

        assert_eq!(ber.id(), IdRef::utf8_string());
        assert_eq!(ber.contents(), &Contents::from(value));
    }

    #[test]
    fn test_from_ber() {
        let value = vec![0x01, 0x02, 0x03];
        let ber = to_ber(&value).unwrap();

        assert_eq!(value, from_ber::<Vec<i32>>(&ber).unwrap());
    }

    #[test]
    fn test_from_ber_indefinite() {
        let value = vec![0x01, 0x02, 0x03];
        let ber = to_ber(&value).unwrap();
        let mut ber = unsafe { Ber::new_indefinite(IdRef::sequence(), ber.contents()) };
        ber.extend_from_slice(BerRef::eoc());

        assert_eq!(value, from_ber::<Vec<i32>>(&ber).unwrap());
    }

    #[test]
    fn test_from_der() {
        let value = vec![0x01, 0x02, 0x03];
        let der = to_der(&value).unwrap();

        assert_eq!(value, from_der::<Vec<i32>>(&der).unwrap());
    }

    #[test]
    fn test_write_der() {
        let value = true;
        let der = to_der(&value).unwrap();

        let mut buffer: Vec<u8> = Vec::new();
        write_der(&value, &mut buffer).unwrap();

        assert_eq!(&buffer[..], der.as_ref() as &[u8]);
    }

    #[test]
    fn test_write_ber() {
        let value = 0x1234i32;
        let der = to_der(&value).unwrap();

        let mut buffer: Vec<u8> = Vec::new();
        write_der(&value, &mut buffer).unwrap();

        assert_eq!(&buffer[..], der.as_ref() as &[u8]);
    }

    #[test]
    fn test_read_der() {
        let value = 0x1234i32;

        let mut buffer: Vec<u8> = Vec::new();
        write_der(&value, &mut buffer).unwrap();

        let value2 = read_der::<_, i32>(&mut &buffer[..]).unwrap();
        assert_eq!(value, value2);
    }

    #[test]
    fn test_read_ber() {
        let value = 0x1234i32;

        let mut buffer: Vec<u8> = Vec::new();
        write_ber(&value, &mut buffer).unwrap();

        let value2 = read_ber::<_, i32>(&mut &buffer[..]).unwrap();
        assert_eq!(value, value2);
    }

    #[test]
    fn test_parse_der() {
        let value = 0x1234i32;

        let mut buffer: Vec<u8> = Vec::new();
        write_der(&value, &mut buffer).unwrap();

        let value2 = parse_der(&mut &buffer[..]).unwrap();
        assert_eq!(value, value2);
    }

    #[test]
    fn test_parse_ber() {
        let value = 0x1234i32;

        let mut buffer: Vec<u8> = Vec::new();
        write_ber(&value, &mut buffer).unwrap();

        let value2 = parse_ber(&mut &buffer[..]).unwrap();
        assert_eq!(value, value2);
    }

    struct NoneDerContentsLen(i16);

    impl ser::Serialize for NoneDerContentsLen {
        fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
            self.0.write_id(buffer)
        }

        fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
            self.0.write_der_contents(buffer)
        }

        fn id_len(&self) -> Result<Option<usize>, Error> {
            self.0.id_len()
        }

        fn der_contents_len(&self) -> Result<Option<usize>, Error> {
            Ok(None)
        }
    }

    #[test]
    fn test_write_none_der_contents_len_into_der() {
        for i in i16::MIN..=i16::MAX {
            let var = NoneDerContentsLen(i);
            assert_eq!(to_der(&var).unwrap(), to_der(&i).unwrap());
        }

        let mut va: Vec<NoneDerContentsLen> = Vec::new();
        let mut vb: Vec<i16> = Vec::new();
        for i in 0..10 {
            assert_eq!(to_der(&va).unwrap(), to_der(&vb).unwrap());

            va.push(NoneDerContentsLen(i));
            vb.push(i);
        }
    }

    #[test]
    fn test_write_none_der_contents_len_into_ber() {
        for i in i16::MIN..=i16::MAX {
            let var = NoneDerContentsLen(i);
            assert_eq!(to_ber(&var).unwrap(), to_ber(&i).unwrap());
        }

        let mut va: Vec<NoneDerContentsLen> = Vec::new();
        let mut vb: Vec<i16> = Vec::new();
        for i in 0..10 {
            assert_eq!(to_ber(&va).unwrap(), to_ber(&vb).unwrap());

            va.push(NoneDerContentsLen(i));
            vb.push(i);
        }
    }

    enum NoneLenEnum {
        NoneDerContentsLen(i16),
        NoneDerContentsLenWrapper(NoneDerContentsLen),
    }

    impl Serialize for NoneLenEnum {
        fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
            match self {
                NoneLenEnum::NoneDerContentsLen(i) => i.write_id(buffer),
                NoneLenEnum::NoneDerContentsLenWrapper(w) => w.write_id(buffer),
            }
        }

        fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
            match self {
                NoneLenEnum::NoneDerContentsLen(i) => i.write_der_contents(buffer),
                NoneLenEnum::NoneDerContentsLenWrapper(w) => w.write_der_contents(buffer),
            }
        }

        fn id_len(&self) -> Result<Option<usize>, Error> {
            match self {
                NoneLenEnum::NoneDerContentsLen(i) => i.id_len(),
                NoneLenEnum::NoneDerContentsLenWrapper(w) => w.id_len(),
            }
        }

        fn der_contents_len(&self) -> Result<Option<usize>, Error> {
            match self {
                NoneLenEnum::NoneDerContentsLen(_) => Ok(None),
                NoneLenEnum::NoneDerContentsLenWrapper(_) => Ok(None),
            }
        }
    }

    #[test]
    fn test_write_none_len_enum_into_der() {
        for i in i16::MIN..=i16::MAX {
            let var = NoneLenEnum::NoneDerContentsLen(i);
            assert_eq!(to_der(&var).unwrap(), to_der(&i).unwrap());

            let var = NoneLenEnum::NoneDerContentsLenWrapper(NoneDerContentsLen(i));
            assert_eq!(to_der(&var).unwrap(), to_der(&i).unwrap());
        }

        let mut va: Vec<NoneLenEnum> = Vec::new();
        let mut vb: Vec<i16> = Vec::new();
        for i in 0..10 {
            assert_eq!(to_der(&va).unwrap(), to_der(&vb).unwrap());

            va.push(NoneLenEnum::NoneDerContentsLen(i));
            vb.push(i);

            va.push(NoneLenEnum::NoneDerContentsLenWrapper(NoneDerContentsLen(
                i,
            )));
            vb.push(i);
        }
    }

    #[test]
    fn test_write_none_der_len_into_ber() {
        for i in i16::MIN..=i16::MAX {
            let var = NoneLenEnum::NoneDerContentsLen(i);
            assert_eq!(to_ber(&var).unwrap(), to_ber(&i).unwrap());

            let var = NoneLenEnum::NoneDerContentsLenWrapper(NoneDerContentsLen(i));
            assert_eq!(to_ber(&var).unwrap(), to_ber(&i).unwrap());
        }

        let mut va: Vec<NoneLenEnum> = Vec::new();
        let mut vb: Vec<i16> = Vec::new();
        for i in 0..10 {
            assert_eq!(to_ber(&va).unwrap(), to_ber(&vb).unwrap());

            va.push(NoneLenEnum::NoneDerContentsLen(i));
            vb.push(i);

            va.push(NoneLenEnum::NoneDerContentsLenWrapper(NoneDerContentsLen(
                i,
            )));
            vb.push(i);
        }
    }
}
