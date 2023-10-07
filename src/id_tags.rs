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

/// `ClassTag` represents Tag class of identifier.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClassTag {
    /// Universal Tag
    Universal = 0x00,
    /// Application Tag
    Application = 0x40,
    /// Context-Specific Tag
    ContextSpecific = 0x80,
    /// Private Tag
    Private = 0xc0,
}

/// `PCTag` represents Primitive/Constructed flag of identifier.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PCTag {
    /// Primitive data type.
    Primitive = 0x00,
    /// Constructed data type.
    Constructed = 0x20,
}

/// `IdNumber` represents the number of identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdNumber(u128);

impl From<u8> for IdNumber {
    fn from(n: u8) -> Self {
        Self(n as u128)
    }
}

impl From<u16> for IdNumber {
    fn from(n: u16) -> Self {
        Self(n as u128)
    }
}

impl From<u32> for IdNumber {
    fn from(n: u32) -> Self {
        Self(n as u128)
    }
}

impl From<u64> for IdNumber {
    fn from(n: u64) -> Self {
        Self(n as u128)
    }
}

impl From<u128> for IdNumber {
    fn from(n: u128) -> Self {
        Self(n)
    }
}

impl From<usize> for IdNumber {
    fn from(n: usize) -> Self {
        Self(n as u128)
    }
}
