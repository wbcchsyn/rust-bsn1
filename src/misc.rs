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

use crate::{Error, Length};
use std::io::{Read, Write};

/// Tries to read one byte from `readable`.
pub fn read_u8<T>(readable: &mut T) -> Result<u8, Error>
where
    T: ?Sized + Read,
{
    let mut buf = [0; 1];
    match readable.read(&mut buf) {
        Err(e) => Err(e.into()),
        Ok(0) => Err(Error::UnTerminatedBytes),
        Ok(1) => Ok(buf[0]),
        _ => unreachable!(),
    }
}

/// Tries to write `byte` to `writeable`.
///
/// # Safety
///
/// The behavior is undefined if `writeable` is closed or broken before this function returns.
/// `writeable` should be `std::io::Sink` or `Buffer`.
pub unsafe fn write_u8<T>(writeable: &mut T, byte: u8) -> Result<(), Error>
where
    T: ?Sized + Write,
{
    let buf = [byte];
    match writeable.write(&buf) {
        Err(e) => Err(e.into()),
        Ok(1) => Ok(()),
        _ => unimplemented!(),
    }
}

/// Parses the identifier and the length from `readable`, writes them to `writeable`,
/// and returns the `Length`.
///
/// # Safety
///
/// The behavior is undefined if `writeable` is closed or broken before this function returns.
/// `writeable` should be `std::io::Sink` or `Buffer`.
pub unsafe fn parse_id_length<R, W>(readable: &mut R, writeable: &mut W) -> Result<Length, Error>
where
    R: ?Sized + Read,
    W: ?Sized + Write,
{
    let _ = crate::identifier_ref::parse_id(readable, writeable)?;
    crate::length::parse_length(readable, writeable)
}
