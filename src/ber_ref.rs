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

use crate::{identifier_ref, length, Ber, ContentsRef, DerRef, Error, IdRef, Length};
use std::borrow::Borrow;
use std::mem;

/// `BerRef` is a wrapper of `[u8]` and represents a BER.
///
/// This struct is 'Unsized' and the user will usually use a reference to the instance.
///
/// # Warnings
///
/// ASN.1 allows BER both 'definite' and 'indefinite' length octets.
/// In case of 'indefinite', the contents must be a sequence of BERs,
/// and must be terminated by 'EOC BER'.
/// (Single 'EOC BER' is allowed.)
///
/// A reference to `BerRef` works fine even if the user violates the rule,
/// however, the inner slice will be invalid as a BER then.
/// Such a slice can not be parsed as a BER again.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct BerRef {
    bytes: [u8],
}

impl BerRef {
    /// Returns a reference to 'End-of-Contents'.
    pub const fn eoc() -> &'static Self {
        const BYTES: [u8; 2] = [0x00, 0x00];
        unsafe { Self::from_bytes_unchecked(&BYTES) }
    }

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a reference to `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// On success, `bytes` will be updated to point the next octet of `BerRef`;
    /// otehrwise, `bytes` will not be updated.
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
    /// use bsn1::{Ber, BerRef};
    ///
    /// // Serializes '8' as an Integer.
    /// let ber = Ber::from(8_u8);
    /// let mut serialized = Vec::from(ber.as_ref() as &[u8]);
    ///
    /// // Deserializes
    /// {
    ///     let mut serialized: &[u8] = &serialized[..];
    ///     let deserialized = BerRef::parse(&mut serialized).unwrap();
    ///     assert_eq!(ber, deserialized);
    ///     assert_eq!(serialized.len(), 0);
    /// }
    ///
    /// // Extra octets at the end does not affect the result.
    /// serialized.push(0x00);
    /// serialized.push(0xff);
    /// {
    ///     let mut serialized: &[u8] = &serialized[..];
    ///     let deserialized = BerRef::parse(&mut serialized).unwrap();
    ///     assert_eq!(ber, deserialized);
    ///     assert_eq!(serialized, &[0x00, 0xff]);
    /// }
    /// ```
    pub fn parse<'a>(bytes: &mut &'a [u8]) -> Result<&'a Self, Error> {
        let init_bytes = *bytes;
        let mut stack_depth: isize = 0;

        while {
            stack_depth += Self::do_parse(bytes)? as isize;
            stack_depth > 0
        } {}

        let total_len = init_bytes.len() - bytes.len();
        unsafe { Ok(Self::from_bytes_unchecked(&init_bytes[..total_len])) }
    }

    /// Parses `bytes` starting with octets of 'ASN.1 BER' and returns a mutable reference to
    /// `BerRef`.
    ///
    /// This function ignores extra octet(s) at the end of `bytes` if any.
    ///
    /// On success, `bytes` will be updated to point the next octet of `BerRef`;
    /// otehrwise, `bytes` will not be updated.
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
    /// use bsn1::{Ber, BerRef};
    ///
    /// // Serialize "Foo" as utf8-string.
    /// let ber = Ber::from("Foo");
    /// let mut serialized = Vec::from(ber.as_ref() as &[u8]);
    ///
    /// // Deserialize.
    /// let deserialized = BerRef::parse_mut(&mut &mut serialized[..]).unwrap();
    /// assert_eq!(ber, deserialized);
    ///
    /// // You can update it because 'deserialized' is a mutable reference.
    /// deserialized.mut_contents()[0] = 'B' as u8;
    /// assert_eq!(Ber::from("Boo").as_ref() as &BerRef, deserialized);
    ///
    /// // Now deserialize represents "Boo", not "Foo".
    ///
    /// // Deserialize again.
    /// let deserialized = BerRef::parse_mut(&mut &mut serialized[..]).unwrap();
    /// assert_eq!(Ber::from("Boo").as_ref() as &BerRef, deserialized);
    /// ```
    pub fn parse_mut<'a>(bytes: &mut &'a mut [u8]) -> Result<&'a mut Self, Error> {
        let read_bytes = {
            let mut readable: &[u8] = *bytes;
            let mut stack_depth: isize = 0;

            while {
                stack_depth += Self::do_parse(&mut readable)? as isize;
                stack_depth > 0
            } {}

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

    fn do_parse(readable: &mut &[u8]) -> Result<i8, Error> {
        // Check eoc
        if readable.starts_with(Self::eoc().as_ref()) {
            *readable = &readable[Self::eoc().as_ref().len()..];
            return Ok(-1);
        }

        let mut writeable = std::io::sink();

        match unsafe { crate::misc::parse_id_length(readable, &mut writeable)? } {
            Length::Definite(contents_len) => {
                if readable.len() < contents_len {
                    Err(Error::UnTerminatedBytes)
                } else {
                    *readable = &readable[contents_len..];
                    Ok(0)
                }
            }
            Length::Indefinite => Ok(1),
        }
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as an 'BER', use [`parse`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`parse`]: Self::parse
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let ber = Ber::from(0x34_u8);
    /// let serialized: &[u8] = ber.as_ref();
    /// let deserialized = unsafe { BerRef::from_bytes_unchecked(serialized) };
    ///
    /// assert_eq!(ber, deserialized);
    /// ```
    pub const unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        mem::transmute(bytes)
    }

    /// Provides a reference from `bytes` without any check.
    ///
    /// `bytes` must be BER octets and must not include any extra octet.
    ///
    /// If it is not sure whether `bytes` are valid octets as a 'BER', use [`parse_mut`] instead.
    ///
    /// # Safety
    ///
    /// The behaviour is undefined if `bytes` is not formatted as a BER.
    ///
    /// [`parse_mut`]: Self::parse_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let ber = Ber::from(0x34_u8);
    /// let mut serialized: Vec<u8> = Vec::from(ber.as_ref() as &[u8]);
    /// let deserialized = unsafe { BerRef::from_mut_bytes_unchecked(&mut serialized[..]) };
    ///
    /// assert_eq!(ber, deserialized);
    ///
    /// deserialized.mut_contents()[0] += 1;
    /// assert_ne!(ber, deserialized);
    /// ```
    pub unsafe fn from_mut_bytes_unchecked(bytes: &mut [u8]) -> &mut Self {
        mem::transmute(bytes)
    }
    /// Provides a reference to the [`IdRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let ber = Ber::from(0x05_u8);
    /// let ber: &BerRef = &ber;
    ///
    /// assert_eq!(ber.id(), IdRef::integer());
    /// ```
    pub fn id(&self) -> &IdRef {
        unsafe { identifier_ref::parse_id_unchecked(&mut &self.bytes) }
    }

    /// Provides a mutable reference to the [`IdRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, ClassTag, IdRef, PCTag};
    ///
    /// let mut ber = Ber::from(0x05_u8);
    /// let ber: &mut BerRef = &mut ber;
    ///
    /// assert_eq!(ber.id(), IdRef::integer());
    ///
    /// assert_eq!(ber.id().class(), ClassTag::Universal);
    /// ber.mut_id().set_class(ClassTag::Private);
    /// assert_eq!(ber.id().class(), ClassTag::Private);
    ///
    /// assert_eq!(ber.id().pc(), PCTag::Primitive);
    /// ber.mut_id().set_pc(PCTag::Constructed);
    /// assert_eq!(ber.id().pc(), PCTag::Constructed);
    /// ```
    pub fn mut_id(&mut self) -> &mut IdRef {
        unsafe {
            let ret = self.id();
            let ptr = ret as *const IdRef;
            let ptr = ptr as *mut IdRef;
            &mut *ptr
        }
    }

    /// Returns the [`Length`] of `self`.
    ///
    /// # Warnings
    ///
    /// `Length` stands for 'the length octets' in BER.
    /// It implies the byte count of `contents` or `indefinite`.
    /// The total byte count is greater than the value even if it is `definite`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, Length};
    ///
    /// let ber = Ber::from(false);
    /// let ber: &BerRef = &ber;
    ///
    /// assert_eq!(ber.length(), Length::Definite(ber.contents().len()));
    /// ```
    pub fn length(&self) -> Length {
        let mut bytes = &self.bytes;
        unsafe {
            identifier_ref::parse_id_unchecked(&mut bytes);
            length::parse_length_unchecked(&mut bytes)
        }
    }

    /// Provides a reference to the [`ContentsRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef};
    ///
    /// let ber = Ber::from(false);
    /// let ber: &BerRef = &ber;
    ///
    /// assert_eq!(ber.contents().to_bool_ber(), Ok(false));
    /// ```
    pub fn contents(&self) -> &ContentsRef {
        self.disassemble().2
    }

    /// Provides a mutable reference to the [`ContentsRef`] of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, ContentsRef};
    ///
    /// let mut ber = Ber::from(false);
    /// let ber: &mut BerRef = &mut ber;
    ///
    /// assert_eq!(ber.contents().to_bool_ber(), Ok(false));
    ///
    /// let true_contents: &ContentsRef = true.into();
    /// ber.mut_contents().as_mut().copy_from_slice(true_contents.as_ref());
    /// assert_eq!(ber.contents().to_bool_ber(), Ok(true));
    /// ```
    pub fn mut_contents(&mut self) -> &mut ContentsRef {
        unsafe {
            let ret = self.contents();
            let ptr = ret as *const ContentsRef;
            let ptr = ptr as *mut ContentsRef;
            &mut *ptr
        }
    }

    /// Returns references to `IdRef`, `Length`, and `ContentsRef` of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Ber, BerRef, IdRef};
    ///
    /// let ber = Ber::from("Foo");
    /// let ber: &BerRef = ber.as_ref();
    ///
    /// let (id, length, contents) = ber.disassemble();
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
}

impl<'a> From<&'a DerRef> for &'a BerRef {
    fn from(der: &'a DerRef) -> Self {
        unsafe { BerRef::from_bytes_unchecked(der.as_ref()) }
    }
}

impl AsRef<[u8]> for BerRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl ToOwned for BerRef {
    type Owned = Ber;

    fn to_owned(&self) -> Self::Owned {
        unsafe { Ber::from_bytes_unchecked(self.as_ref()) }
    }
}

impl<T> PartialEq<T> for BerRef
where
    T: Borrow<BerRef>,
{
    fn eq(&self, other: &T) -> bool {
        self == other.borrow()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_deinite() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let ber = Ber::from(&bytes[..i]);
            let mut bytes: &[u8] = ber.as_ref();
            let parsed = BerRef::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_indefinite() {
        let bers: Vec<Ber> = (0..10).map(Ber::from).collect();

        for i in 0..10 {
            let contents: Vec<u8> = bers[..i]
                .iter()
                .map(|ber| ber.as_ref() as &[u8])
                .flatten()
                .copied()
                .collect();
            let mut ber =
                unsafe { Ber::new_indefinite(IdRef::sequence(), contents.as_slice().into()) };
            ber.extend_from_slice(BerRef::eoc());

            let mut bytes: &[u8] = ber.as_ref();
            let parsed = BerRef::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_deinite_in_definite() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let inner = Ber::from(&bytes[..i]);

            let ber = Ber::new(IdRef::sequence(), (inner.as_ref() as &[u8]).into());
            let mut bytes: &[u8] = ber.as_ref();

            let parsed = BerRef::parse(&mut bytes).unwrap();
            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_indeinite_in_definite() {
        let bers: Vec<Ber> = (0..10).map(Ber::from).collect();
        for i in 0..bers.len() {
            let contents: Vec<u8> = bers[..i]
                .iter()
                .map(|ber| ber.as_ref() as &[u8])
                .flatten()
                .copied()
                .collect();
            let mut inner =
                unsafe { Ber::new_indefinite(IdRef::octet_string(), contents.as_slice().into()) };
            inner.extend_from_slice(BerRef::eoc());

            let ber = Ber::new(IdRef::sequence(), (inner.as_ref() as &[u8]).into());
            let mut bytes: &[u8] = ber.as_ref();

            let parsed = BerRef::parse(&mut bytes).unwrap();
            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_deinite_in_indefinite() {
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        for i in 0..bytes.len() {
            let inner = Ber::from(&bytes[..i]);

            let mut ber =
                unsafe { Ber::new_indefinite(IdRef::sequence(), (inner.as_ref() as &[u8]).into()) };
            ber.extend_from_slice(BerRef::eoc());

            let mut bytes: &[u8] = ber.as_ref();
            let parsed = BerRef::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }

    #[test]
    fn parse_indeinite_in_indefinite() {
        let bers: Vec<Ber> = (0..10).map(Ber::from).collect();
        for i in 0..bers.len() {
            let contents: Vec<u8> = bers[..i]
                .iter()
                .map(|ber| ber.as_ref() as &[u8])
                .flatten()
                .copied()
                .collect();
            let mut inner =
                unsafe { Ber::new_indefinite(IdRef::octet_string(), contents.as_slice().into()) };
            inner.extend_from_slice(BerRef::eoc());

            let mut ber =
                unsafe { Ber::new_indefinite(IdRef::sequence(), (inner.as_ref() as &[u8]).into()) };
            ber.extend_from_slice(BerRef::eoc());

            let mut bytes: &[u8] = ber.as_ref();
            let parsed = BerRef::parse(&mut bytes).unwrap();

            assert_eq!(ber, parsed);
            assert_eq!(bytes.len(), 0);
        }
    }
}
