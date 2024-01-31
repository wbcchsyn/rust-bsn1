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

/// `TagNumber` represents the number of identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TagNumber(u128);

impl From<u8> for TagNumber {
    fn from(n: u8) -> Self {
        Self(n as u128)
    }
}

impl From<u16> for TagNumber {
    fn from(n: u16) -> Self {
        Self(n as u128)
    }
}

impl From<u32> for TagNumber {
    fn from(n: u32) -> Self {
        Self(n as u128)
    }
}

impl From<u64> for TagNumber {
    fn from(n: u64) -> Self {
        Self(n as u128)
    }
}

impl From<u128> for TagNumber {
    fn from(n: u128) -> Self {
        Self(n)
    }
}

impl From<usize> for TagNumber {
    fn from(n: usize) -> Self {
        Self(n as u128)
    }
}

impl TagNumber {
    /// Returns the inner number.
    pub fn get(&self) -> u128 {
        self.0
    }
}
