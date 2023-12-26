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

use crate::{Error, Length};
use std::io::{Read, Write};

/// Tries to read one byte from `readable`.
pub fn read_u8<T: Read>(readable: &mut T) -> Result<u8, Error> {
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
pub unsafe fn write_u8<T: Write>(writeable: &mut T, byte: u8) -> Result<(), Error> {
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
pub unsafe fn parse_id_length<R: Read, W: Write>(
    readable: &mut R,
    writeable: &mut W,
) -> Result<Length, Error> {
    let _ = crate::identifier_ref::parse_id(readable, writeable)?;
    crate::length::parse_length(readable, writeable)
}
