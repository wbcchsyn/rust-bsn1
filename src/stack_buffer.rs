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

use core::mem::size_of;
use core::ops::Deref;
use core::ops::{Index, IndexMut};

#[derive(Clone, Copy)]
pub struct StackBuffer {
    buffer: [u8; Self::CAPACITY],
    len_: u8,
}

impl StackBuffer {
    const CAPACITY: usize = size_of::<i128>() + 1;
}

impl StackBuffer {
    pub const fn new() -> Self {
        Self {
            buffer: [0; Self::CAPACITY],
            len_: 0,
        }
    }
}

impl AsRef<[u8]> for StackBuffer {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl Deref for StackBuffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl Index<usize> for StackBuffer {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            let ptr = self.as_ptr().add(index);
            &*ptr
        }
    }
}

impl IndexMut<usize> for StackBuffer {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe {
            let ptr = self.as_mut_ptr().add(index);
            &mut *ptr
        }
    }
}

impl StackBuffer {
    /// # Safety
    ///
    /// The behavior is undefined if the length will exceeds the capacity.
    pub unsafe fn push(&mut self, val: u8) {
        debug_assert!(self.len() < self.capacity());

        self.buffer[self.len()] = val;
        self.len_ += 1;
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.buffer.as_ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.buffer.as_mut_ptr()
    }

    pub const fn len(&self) -> usize {
        self.len_ as usize
    }

    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        self.len_ = new_len as u8
    }

    pub const fn capacity(&self) -> usize {
        Self::CAPACITY
    }
}

#[cfg(test)]
mod stack_buffer_tests {
    use super::*;

    #[test]
    fn new() {
        let buffer = StackBuffer::new();
        assert_eq!(0, buffer.len());
    }

    #[test]
    fn push() {
        let mut buffer = StackBuffer::new();
        let mut v = Vec::new();

        for i in 0..StackBuffer::CAPACITY {
            assert_eq!(i, buffer.len());

            unsafe { buffer.push(i as u8) };
            v.push(i as u8);

            assert_eq!(v.as_ref() as &[u8], buffer.as_ref());
        }

        assert_eq!(buffer.capacity(), buffer.len());
    }
}
