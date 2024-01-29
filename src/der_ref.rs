// Copyright 2021-2024 Shin Yoshida
//
// "GPL-3.0-only"
//
// This is part of BSN1
//
// BSN1 is free software: you can redistribute it and/or modify it under the terms of the
// GNU General Public License as published by the Free Software Foundation, version 3.
//
// BSN1 is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
// even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with this program. If
// not, see <https://www.gnu.org/licenses/>.

use crate::{identifier_ref, length, ContentsRef, Der, Error, IdRef, Length};
use std::borrow::Borrow;

/// `DerRef` is a wrapper of `[u8]` and represents DER.
///
/// This struct is 'Unsized', and the user will usually use a reference.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct DerRef {
    bytes: [u8],
}

impl DerRef {
    /// Returns a reference to 'boolean DER' of `val`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{DerRef, IdRef};
    ///
    /// let true_ = DerRef::boolean(true);
    /// assert_eq!(true_.id(), IdRef::boolean());
    /// assert_eq!(true_.contents().to_bool_der(), Ok(true));
    ///
    /// let false_ = DerRef::boolean(false);
    /// assert_eq!(false_.id(), IdRef::boolean());
    /// assert_eq!(false_.contents().to_bool_der(), Ok(false));
    /// ```
    pub const fn boolean(val: bool) -> &'static Self {
        match val {
            true => unsafe { Self::from_bytes_unchecked(&[0x01, 0x01, 0xff]) },
            false => unsafe { Self::from_bytes_unchecked(&[0x01, 0x01, 0x00]) },
        }
    }

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a reference to `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// On success, `bytes` is updated to point the next octet of `DerRef`;
    /// otherwise, `bytes` is not updated.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// // Serializes '8' as Integer.
    /// let der = Der::from(8_i32);
    /// let mut serialized = Vec::from(der.as_ref() as &[u8]);
    ///
    /// // Deserialize
    /// {
    ///     let mut serialized: &[u8] = &serialized[..];
    ///     let deserialized = DerRef::parse(&mut serialized).unwrap();
    ///     assert_eq!(der, deserialized);
    ///     assert_eq!(serialized.len(), 0);
    /// }
    ///
    /// // The result is not changed even if extra octets are added to the end.
    /// serialized.push(0xff);
    /// serialized.push(0x00);
    ///
    /// {
    ///     let mut serialized: &[u8] = &serialized[..];
    ///     let deserialized = DerRef::parse(&mut serialized).unwrap();
    ///     assert_eq!(der, deserialized);
    ///     assert_eq!(serialized, &[0xff, 0x00]);
    /// }
    /// ```
    pub fn parse<'a>(bytes: &mut &'a [u8]) -> Result<&'a Self, Error> {
        let init_bytes = *bytes;
        Self::do_parse(bytes)?;

        let total_len = init_bytes.len() - bytes.len();
        let read = &init_bytes[..total_len];
        unsafe { Ok(Self::from_bytes_unchecked(read)) }
    }

    /// Parses `bytes` starting with octets of 'ASN.1 DER' and returns a mutable reference to
    /// `DerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// On success, `bytes` is updated to point the next octet of `DerRef`;
    /// otherwise, `bytes` is not updated.
    ///
    /// # Warnings
    ///
    /// ASN.1 does not allow some universal identifiers for DER, however, this function accepts
    /// such an identifier.
    /// For example, 'Octet String' must be primitive in DER, but this function returns `Ok` for
    /// constructed Octet String DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// // Serialize "Foo" as utf8-string.
    /// let der = Der::from("Foo");
    /// let mut serialized = Vec::from(der.as_ref() as &[u8]);
    ///
    /// // Deserialize.
    /// {
    ///     let mut serialized: &mut [u8] = serialized.as_mut();
    ///     let deserialized = DerRef::parse_mut(&mut serialized).unwrap();
    ///     assert_eq!(der, deserialized);
    ///     assert_eq!(serialized.len(), 0);
    ///
    ///     deserialized.mut_contents()[0] = 'B' as u8;
    ///     assert_eq!(deserialized.contents().as_ref(), "Boo".as_bytes());
    /// }
    ///
    /// // Now `serialized` represents "Boo", not "Foo", because we changed via `deserialized`.
    ///
    /// // Deserialize again.
    /// {
    ///     let mut serialized: &mut [u8] = serialized.as_mut();
    ///     let deserialized = DerRef::parse_mut(&mut serialized).unwrap();
    ///
    ///     assert_eq!(serialized.len(), 0);
    ///     assert_ne!(der, deserialized);
    ///     assert_eq!(deserialized.contents().as_ref(), "Boo".as_bytes());
    /// }
    /// ```
    pub fn parse_mut<'a>(bytes: &mut &'a mut [u8]) -> Result<&'a mut Self, Error> {
        let read_bytes = {
            let mut readable: &[u8] = *bytes;
            Self::do_parse(&mut readable)?;

            bytes.len() - readable.len()
        };

        unsafe {
            let init_ptr = bytes.as_mut_ptr();
            let left_bytes = bytes.len() - read_bytes;
            *bytes = std::slice::from_raw_parts_mut(init_ptr.add(read_bytes), left_bytes);

            let read = std::slice::from_raw_parts_mut(init_ptr, read_bytes);
            Ok(Self::from_mut_bytes_unchecked(read))
        }
    }

    fn do_parse(readable: &mut &[u8]) -> Result<(), Error> {
        let mut writeable = std::io::sink();

        let length = match unsafe { crate::misc::parse_id_length(readable, &mut writeable)? } {
            Length::Indefinite => return Err(Error::IndefiniteLength),
            Length::Definite(length) => length,
        };

        if readable.len() < length {
            Err(Error::UnTerminatedBytes)
        } else {
            *readable = &readable[length..];
            Ok(())
        }
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as a 'DER', use [`parse`] instead.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// let der = Der::from(8_i32);
    /// let serialized: Vec<u8> = Vec::from(der.as_ref() as &[u8]);
    /// let deserialized = unsafe { DerRef::from_bytes_unchecked(&serialized[..]) };
    ///
    /// assert_eq!(der, deserialized);
    /// ```
    pub const unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        std::mem::transmute(bytes)
    }

    /// Provides a mutable reference from `bytes` without any check.
    ///
    /// `bytes` must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` is valid octets as a 'DER', use [`parse_mut`] instead.
    ///
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a DER.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// let der = Der::from(8_i32);
    /// let mut serialized: Vec<u8> = Vec::from(der.as_ref() as &[u8]);
    /// let deserialized = unsafe { DerRef::from_mut_bytes_unchecked(&mut serialized[..]) };
    ///
    /// assert_eq!(der, deserialized);
    ///
    /// deserialized.mut_contents()[0] += 1;
    ///
    /// assert_ne!(der, deserialized);
    /// ```
    pub unsafe fn from_mut_bytes_unchecked(bytes: &mut [u8]) -> &mut Self {
        std::mem::transmute(bytes)
    }

    /// Returns a reference to the `IdRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, IdRef};
    ///
    /// let der = Der::from(4_i32);
    /// let der: &DerRef = der.as_ref();
    /// assert_eq!(IdRef::integer(), der.id());
    /// ```
    pub fn id(&self) -> &IdRef {
        unsafe { identifier_ref::parse_id_unchecked(&mut &self.bytes) }
    }

    /// Returns a mutable reference to the `IdRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{ClassTag, Der, DerRef, PCTag};
    ///
    /// let mut der = Der::from(4_i32);
    /// let der: &mut DerRef = der.as_mut();
    ///
    /// assert_eq!(der.id().class(), ClassTag::Universal);
    /// der.mut_id().set_class(ClassTag::Private);
    /// assert_eq!(der.id().class(), ClassTag::Private);
    ///
    /// assert_eq!(der.id().pc(), PCTag::Primitive);
    /// der.mut_id().set_pc(PCTag::Constructed);
    /// assert_eq!(der.id().pc(), PCTag::Constructed);
    /// ```
    pub fn mut_id(&mut self) -> &mut IdRef {
        self.disassemble_mut().0
    }

    /// Returns `Length` of `self`.
    ///
    /// Note that DER does not allow indefinite Length.
    /// The return value is always `Length::Definite`.
    ///
    /// # Warnings
    ///
    /// `Length` stands for the length octets in DER: i.e. the length of the 'contents octets'.
    /// The total byte count of the DER is greater than the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, Length};
    ///
    /// let der = Der::from("Foo");
    /// let der: &DerRef = der.as_ref();
    ///
    /// assert_eq!(Length::Definite("Foo".len()), der.length());
    /// ```
    pub fn length(&self) -> Length {
        self.disassemble().1
    }

    /// Returns a reference to the contents octets of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// let der = Der::from("Foo");
    /// let der: &DerRef = der.as_ref();
    ///
    /// assert_eq!(der.contents().as_ref(), "Foo".as_bytes());
    /// ```
    pub fn contents(&self) -> &ContentsRef {
        self.disassemble().2
    }

    /// Returns a mutable reference to the 'contents octets' of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef};
    ///
    /// let mut der = Der::from("Foo");
    /// let der: &mut DerRef = der.as_mut();
    ///
    /// assert_eq!(der.contents().as_ref(), "Foo".as_bytes());
    ///
    /// der.mut_contents()[0] = 'B' as u8;
    /// assert_eq!(der.contents().as_ref(), "Boo".as_bytes());
    /// ```
    pub fn mut_contents(&mut self) -> &mut ContentsRef {
        self.disassemble_mut().2
    }

    /// Returns references to `IdRef`, `Length`, and `ContentsRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, IdRef};
    ///
    /// let der = Der::from("Foo");
    /// let der: &DerRef = der.as_ref();
    ///
    /// let (id, length, contents) = der.disassemble();
    ///
    /// assert_eq!(id, IdRef::utf8_string());
    /// assert_eq!(length.definite().unwrap(), "Foo".len());
    /// assert_eq!(contents.as_ref(), "Foo".as_bytes());
    /// ```
    pub fn disassemble(&self) -> (&IdRef, Length, &ContentsRef) {
        let mut bytes = &self.bytes;

        let id = unsafe { identifier_ref::parse_id_unchecked(&mut bytes) };
        let length = unsafe { length::parse_length_unchecked(&mut bytes) };
        let contents = bytes.into();

        (id, length, contents)
    }

    /// Returns mutable references to `IdRef`, `Length`, and `ContentsRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Der, DerRef, IdRef};
    ///
    /// let mut der = Der::from("Foo");
    /// let der: &mut DerRef = der.as_mut();
    ///
    /// let (id, length, contents) = der.disassemble_mut();
    ///
    /// assert_eq!(id, IdRef::utf8_string());
    /// assert_eq!(length.definite().unwrap(), "Foo".len());
    /// assert_eq!(contents.as_ref(), "Foo".as_bytes());
    ///
    /// contents[0] = 'B' as u8;
    /// assert_eq!(der.contents().as_ref() as &[u8], "Boo".as_bytes());
    /// ```
    pub fn disassemble_mut(&mut self) -> (&mut IdRef, Length, &mut ContentsRef) {
        let (id, length, contents) = self.disassemble();

        let id_ptr = id as *const IdRef;
        let id_ptr = id_ptr as *mut IdRef;
        let contents_ptr = contents as *const ContentsRef;
        let contents_ptr = contents_ptr as *mut ContentsRef;

        unsafe { (&mut *id_ptr, length, &mut *contents_ptr) }
    }
}

impl AsRef<[u8]> for DerRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for DerRef {
    type Owned = Der;

    fn to_owned(&self) -> Self::Owned {
        unsafe { Der::from_bytes_unchecked(self.as_ref()) }
    }
}

impl<T> PartialEq<T> for DerRef
where
    T: Borrow<DerRef>,
{
    fn eq(&self, other: &T) -> bool {
        self == other.borrow()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_single() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let der = Der::from(&bytes[..i]);
            let mut bytes: &[u8] = der.as_ref();
            let parsed = DerRef::parse(&mut bytes).unwrap();

            assert_eq!(der, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_recursive() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let inner = Der::from(&bytes[..i]);
            let der = Der::new(IdRef::sequence(), (inner.as_ref() as &[u8]).into());

            let mut bytes: &[u8] = der.as_ref();
            let parsed = DerRef::parse(&mut bytes).unwrap();

            assert_eq!(der, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }
}
