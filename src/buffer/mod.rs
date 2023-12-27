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

#[cfg(target_endian = "little")]
mod little_endian;

#[cfg(any(test, target_endian = "big"))]
mod universal_endian;

#[cfg(target_endian = "little")]
pub use little_endian::Buffer;

#[cfg(target_endian = "big")]
pub use universal_endian::Buffer;

type Inner = Buffer;

use std::borrow::Borrow;
use std::ops::Deref;

#[derive(Clone)]
pub struct TmpBuffer(Inner);

impl From<&[u8]> for TmpBuffer {
    fn from(slice: &[u8]) -> Self {
        let mut buf = Self::with_capacity(slice.len());
        unsafe { buf.extend_from_slice(slice) };
        buf
    }
}

impl<const N: usize> From<&[u8; N]> for TmpBuffer {
    fn from(slice: &[u8; N]) -> Self {
        Self::from(&slice[..])
    }
}

impl From<Vec<u8>> for TmpBuffer {
    fn from(vec: Vec<u8>) -> Self {
        Self::from_vec(vec)
    }
}

impl TmpBuffer {
    pub const fn new() -> Self {
        Self(Inner::new())
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self(Inner::with_capacity(cap))
    }

    fn from_vec(vals: Vec<u8>) -> Self {
        Self(Inner::from_vec(vals))
    }

    /// # Safety
    ///
    /// The behaviour is undefined if the length will exceeds the capacity.
    pub unsafe fn push(&mut self, v: u8) {
        self.0.push(v);
    }

    /// # Safety
    ///
    /// The behaviour is undefined if the length will exceeds the capacity.
    pub unsafe fn extend_from_slice(&mut self, vals: &[u8]) {
        self.0.extend_from_slice(vals);
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional);
    }

    pub unsafe fn set_len(&mut self, len: usize) {
        debug_assert!(len <= self.capacity());
        self.0.set_len(len);
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.0.as_ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.0.as_mut_ptr()
    }

    pub fn as_slice(&self) -> &[u8] {
        self.0.as_slice()
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }

    pub fn into_vec(self) -> Vec<u8> {
        self.0.into_vec()
    }
}

impl Borrow<[u8]> for TmpBuffer {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl Deref for TmpBuffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
