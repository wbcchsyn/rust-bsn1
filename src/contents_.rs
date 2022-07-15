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

//! Public module `contents` is deprecated.
//! This module is private and will be renamed as `contents` after current `contents` is deleted.

use crate::Buffer;
use core::borrow::{Borrow, BorrowMut};
use core::mem;
use core::ops::{Deref, DerefMut};

/// `ContentsRef` is a wrapper of [u8] and represents contents octets of ASN.1.
///
/// The user can access to the inner bytes via `Deref` and `DerefMut` implementation.
///
/// This struct is `Unsized`, and user will usually uses a reference to the instance.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentsRef {
    bytes: [u8],
}

impl<'a> From<&'a [u8]> for &'a ContentsRef {
    /// This function is same to `ContentsRef::from_bytes`.
    fn from(bytes: &'a [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl<'a> From<&'a mut [u8]> for &'a mut ContentsRef {
    /// This function is same to `ContentsRef::from_bytes_mut`.
    fn from(bytes: &'a mut [u8]) -> Self {
        unsafe { mem::transmute(bytes) }
    }
}

impl ContentsRef {
    /// Creates a reference to `ContentsRef` holding `bytes`.
    ///
    /// This function is same to `<&ContentsRef>::from`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let bytes: &[u8] = &[1, 2, 3];
    /// let contents = ContentsRef::from_bytes(bytes);
    ///
    /// assert_eq!(contents as &[u8], bytes);
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> &Self {
        <&ContentsRef>::from(bytes)
    }

    /// Creates a mutable reference to `ContentsRef` holding `bytes`.
    ///
    /// This function is same to `<&mut ContentsRef>::from`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bsn1::ContentsRef;
    ///
    /// let bytes: &mut [u8] = &mut [1, 2, 3];
    /// let contents = ContentsRef::from_bytes(bytes);
    ///
    /// assert_eq!(contents as &[u8], &[1, 2, 3]);
    /// ```
    pub fn from_bytes_mut(bytes: &mut [u8]) -> &mut Self {
        <&mut ContentsRef>::from(bytes)
    }
}

impl AsRef<[u8]> for ContentsRef {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

impl AsMut<[u8]> for ContentsRef {
    fn as_mut(&mut self) -> &mut [u8] {
        self
    }
}

impl Borrow<[u8]> for ContentsRef {
    fn borrow(&self) -> &[u8] {
        self
    }
}

impl BorrowMut<[u8]> for ContentsRef {
    fn borrow_mut(&mut self) -> &mut [u8] {
        self
    }
}

impl Deref for ContentsRef {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}

impl DerefMut for ContentsRef {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bytes
    }
}

/// `Contents` owns `ContentsRef` and represents contents octets of ASN.1.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Contents {
    buffer: Buffer,
}

impl AsRef<[u8]> for Contents {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

impl AsRef<ContentsRef> for Contents {
    fn as_ref(&self) -> &ContentsRef {
        self
    }
}

impl AsMut<[u8]> for Contents {
    fn as_mut(&mut self) -> &mut [u8] {
        self
    }
}

impl Deref for Contents {
    type Target = ContentsRef;

    fn deref(&self) -> &Self::Target {
        ContentsRef::from_bytes(self.buffer.as_ref())
    }
}

impl DerefMut for Contents {
    fn deref_mut(&mut self) -> &mut Self::Target {
        ContentsRef::from_bytes_mut(self.buffer.as_mut())
    }
}
