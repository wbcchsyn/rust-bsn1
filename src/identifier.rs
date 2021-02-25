// Copyright 2021 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause"
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
//
//
// Redistribution and use in source and binary forms, with or without modification, are permitted
// provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice, this
//    list of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
// INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

use crate::Buffer;
use core::ops::Deref;

/// `ClassTag` is u8 enum for Tag class of Identifier in 'ASN.1.'
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

/// `PCTag` is u8 enum for Private/Constructed flag of Identifier in 'ASN.1.'
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PCTag {
    /// Primitive data type.
    Primitive = 0x00,
    /// Constructed data type.
    Constructed = 0x20,
}

/// `IdRef` represents Identifier octets in 'ASN.1.'
///
/// This struct is `Unsized` , so usually thay use a reference to it.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdRef {
    bytes: [u8],
}

impl IdRef {
    /// Builds instance from `bytes` without any sanitize.
    /// `bytes` must not include any extra octets.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if the format of `bytes` is not right.
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        let ptr = bytes as *const [u8];
        let ptr = ptr as *const IdRef;
        &*ptr
    }
}

/// `Id` owns `IdRef` and represents Identifier octets in 'ASN.1.'
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id {
    buffer: Buffer,
}

impl Deref for Id {
    type Target = IdRef;

    fn deref(&self) -> &Self::Target {
        unsafe { IdRef::from_bytes_unchecked(self.buffer.as_ref()) }
    }
}
