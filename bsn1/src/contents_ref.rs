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

use crate::{Contents, Error};
use num::PrimInt;
use std::borrow::{Borrow, ToOwned};
use std::mem;
use std::mem::MaybeUninit;
use std::ops::{Index, IndexMut};
use std::slice::SliceIndex;

/// `ContentsRef` is a wrapper of `[u8]` and represents 'ASN.1 contents'.
///
/// The user can access the inner slice via the implementation of `AsRef` or `AsMut`.
///
/// This struct is `Unsized`, and the user will usually use a reference.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ContentsRef {
    bytes: [u8],
}

impl ContentsRef {
    /// Returns the byte count of the inner slice.
    ///
    /// # Example
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let bytes = &[0, 1, 2, 3, 4];
    /// let contents = <&ContentsRef>::from(bytes);
    ///
    /// assert_eq!(contents.len(), bytes.len());
    /// ```    
    pub const fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns `true` if the inner slice is empty, or `false`.
    ///
    /// # Example
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let bytes = &[];
    /// let contents = <&ContentsRef>::from(bytes);
    /// assert_eq!(contents.is_empty(), true);
    ///
    /// let bytes = &[0, 1, 2, 3, 4];
    /// let contents = <&ContentsRef>::from(bytes);
    /// assert_eq!(contents.is_empty(), false);
    /// ```    
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Parses `self` as the ASN.1 contents of integer.
    ///
    /// Type `T` should be a built-in primitive integer type (e.g., u8, i32, isize, i128...)
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::{Contents, ContentsRef};
    ///
    /// let contents = Contents::from(17_i32);
    /// assert_eq!(Ok(17_i32), contents.to_integer::<i32>());
    ///
    /// // Overflow to convert i32::MAX into i16.
    /// let contents = Contents::from(i32::MAX);
    /// assert!(contents.to_integer::<i16>().is_err());
    ///
    /// // Cannot convert a negatibe value into unsigned type.
    /// let contents = Contents::from(-5_i32);
    /// assert!(contents.to_integer::<u32>().is_err());
    /// ```
    pub fn to_integer<T>(&self) -> Result<T, Error>
    where
        T: PrimInt,
    {
        if self.is_empty() {
            return Err(Error::UnterminatedBytes);
        }

        if 1 < self.len() {
            if (self[0] == 0) && (self[1] & 0x80 == 0x00) {
                return Err(Error::RedundantBytes);
            }
            if (self[0] == 0xff) && (self[1] & 0x80 == 0x80) {
                return Err(Error::RedundantBytes);
            }
        }

        // If 'T' is Unsigned type and the first octet is 0x00,
        // We can ignore the first byte 0x00.
        let bytes = if self[0] == 0x00 {
            &self[1..]
        } else {
            self.as_ref()
        };
        if mem::size_of::<T>() < bytes.len() {
            return Err(Error::OverFlow);
        }

        let v = unsafe { self.to_integer_unchecked() };

        if self[0] & 0x80 == 0x00 {
            if v < T::zero() {
                return Err(Error::OverFlow);
            }
        } else {
            if T::zero() <= v {
                return Err(Error::OverFlow);
            }
        }

        Ok(v)
    }

    /// Parses `self` as a contents of ASN.1 integer without any check.
    ///
    /// Type `T` should be a built-in primitive integer type (e.g., u8, i32, isize, u128, ...)
    ///
    /// # Safety
    ///
    /// The behaviour is undefined in the following cases.
    ///
    /// - `self` is not formatted as the contents of ASN.1 integer.
    /// - The value is greater than the max value of `T`, or less than the min value of `T`.
    pub unsafe fn to_integer_unchecked<T>(&self) -> T
    where
        T: PrimInt,
    {
        // If 'T' is Unsigned type and the first octet is 0x00,
        // We can ignore the first byte 0x00.
        let bytes = if self[0] == 0x00 {
            &self[1..]
        } else {
            self.as_ref()
        };
        let filler = if self[0] & 0x80 == 0x00 { 0x00 } else { 0xff };

        let mut be: MaybeUninit<T> = MaybeUninit::uninit();
        be.as_mut_ptr().write_bytes(filler, 1);

        let dst = be.as_mut_ptr() as *mut u8;
        let dst = dst.add(mem::size_of::<T>() - bytes.len());

        dst.copy_from_nonoverlapping(bytes.as_ptr(), bytes.len());

        T::from_be(be.assume_init())
    }

    /// Parses `self` as the contents of BER bool.
    ///
    /// # Warnings
    ///
    /// The rule of BER bool is different from that of DER and CER.
    /// BER regards 0x00 as `False`, and any octet except for 0x00 as `True`.
    ///
    /// See also [`to_bool_der`].
    ///
    /// [`to_bool_der`]: Self::to_bool_der
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let true_contents = <&ContentsRef>::from(true);
    /// assert_eq!(Ok(true), true_contents.to_bool_ber());
    ///
    /// let false_contents = <&ContentsRef>::from(false);
    /// assert_eq!(Ok(false), false_contents.to_bool_ber());
    /// ```
    pub const fn to_bool_ber(&self) -> Result<bool, Error> {
        if self.is_empty() {
            Err(Error::UnterminatedBytes)
        } else if 1 < self.len() {
            Err(Error::ExtraContentsOctet)
        } else if self.bytes[0] == 0x00 {
            Ok(false)
        } else {
            Ok(true)
        }
    }

    /// Parses `self` as the contents of DER bool.
    ///
    /// # Warnings
    ///
    /// The rule of BER bool is different from that of DER and CER.
    /// DER regards 0xFF as `True`, and 0x00 as `False`.
    ///
    /// See also [`to_bool_ber`].
    ///
    /// [`to_bool_ber`]: Self::to_bool_ber
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let true_contents = <&ContentsRef>::from(true);
    /// assert_eq!(Ok(true), true_contents.to_bool_der());
    ///
    /// let false_contents = <&ContentsRef>::from(false);
    /// assert_eq!(Ok(false), false_contents.to_bool_der());
    /// ```
    pub const fn to_bool_der(&self) -> Result<bool, Error> {
        if self.is_empty() {
            Err(Error::UnterminatedBytes)
        } else if 1 < self.len() {
            Err(Error::ExtraContentsOctet)
        } else {
            match self.bytes[0] {
                0x00 => Ok(false),
                0xff => Ok(true),
                _ => Err(Error::InvalidDerBooleanContents),
            }
        }
    }
}

impl<'a> From<&'a [u8]> for &'a ContentsRef {
    fn from(bytes: &'a [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl<'a, const N: usize> From<&'a [u8; N]> for &'a ContentsRef {
    fn from(bytes: &'a [u8; N]) -> Self {
        Self::from(&bytes[..])
    }
}

impl<'a> From<&'a mut [u8]> for &'a mut ContentsRef {
    fn from(bytes: &'a mut [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl<'a, const N: usize> From<&'a mut [u8; N]> for &'a mut ContentsRef {
    fn from(bytes: &'a mut [u8; N]) -> Self {
        Self::from(&mut bytes[..])
    }
}

impl<'a> From<&'a str> for &'a ContentsRef {
    fn from(s: &'a str) -> Self {
        Self::from(s.as_bytes())
    }
}

impl From<bool> for &'static ContentsRef {
    /// The encoding rule of boolean is different between BER and DER.
    /// The return value is valid both as BER and DER.
    fn from(val: bool) -> Self {
        if val {
            Self::from(&[0xff])
        } else {
            Self::from(&[0x00])
        }
    }
}

impl AsRef<[u8]> for ContentsRef {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl AsMut<[u8]> for ContentsRef {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}

impl<T> Index<T> for ContentsRef
where
    T: SliceIndex<[u8]>,
{
    type Output = T::Output;

    fn index(&self, index: T) -> &Self::Output {
        &self.as_ref()[index]
    }
}

impl<T> IndexMut<T> for ContentsRef
where
    T: SliceIndex<[u8]>,
{
    fn index_mut(&mut self, index: T) -> &mut Self::Output {
        &mut self.bytes[index]
    }
}

impl<T> PartialEq<T> for ContentsRef
where
    T: Borrow<ContentsRef>,
{
    fn eq(&self, other: &T) -> bool {
        self.as_ref() == other.borrow().as_ref()
    }
}

impl ToOwned for ContentsRef {
    type Owned = Contents;

    fn to_owned(&self) -> Self::Owned {
        Contents::from(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_bool() {
        // True
        {
            let contents = <&ContentsRef>::from(true);
            assert_eq!(&[0xff], contents.as_ref());
        }

        // false
        {
            let contents = <&ContentsRef>::from(false);
            assert_eq!(&[0x00], contents.as_ref());
        }
    }
}
