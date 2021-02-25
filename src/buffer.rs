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

use core::alloc::Layout;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::mem::size_of;
use core::mem::MaybeUninit;
use core::ptr::null_mut;
use std::alloc::handle_alloc_error;
use std::borrow::Borrow;
use std::fmt;

pub struct Buffer {
    len_: isize,
    buffer: (*mut u8, usize),
}

impl Drop for Buffer {
    fn drop(&mut self) {
        if self.is_stack() {
            return;
        } else {
            let layout = Layout::array::<u8>(self.capacity()).unwrap();
            let ptr = self.as_mut_ptr();
            unsafe { std::alloc::dealloc(ptr, layout) };
        }
    }
}

impl From<&[u8]> for Buffer {
    fn from(vals: &[u8]) -> Self {
        let mut ret = Self::with_capacity(vals.len());
        ret.extend_from_slice(vals);
        ret
    }
}

impl Clone for Buffer {
    fn clone(&self) -> Self {
        if self.is_stack() {
            let mut ret = MaybeUninit::<Self>::uninit();
            let ptr = ret.as_mut_ptr();
            unsafe {
                ptr.copy_from_nonoverlapping(self, 1);
                ret.assume_init()
            }
        } else {
            Self::from(self.as_ref())
        }
    }
}

impl Buffer {
    pub const fn new() -> Self {
        Self {
            len_: isize::MIN,
            buffer: (null_mut(), 0),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let mut ret = Self::new();
        ret.reserve(capacity);
        ret
    }
}

impl AsRef<[u8]> for Buffer {
    fn as_ref(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl AsMut<[u8]> for Buffer {
    fn as_mut(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl fmt::Debug for Buffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let contents: &[u8] = self.as_ref();
        f.debug_tuple("Buffer").field(&contents).finish()
    }
}

impl Borrow<[u8]> for Buffer {
    fn borrow(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl Hash for Buffer {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        let this: &[u8] = self.borrow();
        this.hash(hasher);
    }
}

impl<T> PartialEq<T> for Buffer
where
    T: Borrow<[u8]>,
{
    fn eq(&self, other: &T) -> bool {
        let this: &[u8] = self.borrow();
        let other: &[u8] = other.borrow();
        this == other
    }
}

impl Eq for Buffer {}

impl<T> PartialOrd<T> for Buffer
where
    T: Borrow<[u8]>,
{
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        let this: &[u8] = self.borrow();
        let other: &[u8] = other.borrow();
        this.partial_cmp(other)
    }
}

impl Ord for Buffer {
    fn cmp(&self, other: &Self) -> Ordering {
        let this: &[u8] = self.borrow();
        let other: &[u8] = other.borrow();
        this.cmp(other)
    }
}

impl Buffer {
    pub fn push(&mut self, val: u8) {
        self.reserve(1);
        unsafe {
            let ptr = self.as_mut_ptr().add(self.len());
            *ptr = val;
        }
        self.len_ += 1;
    }

    pub fn extend_from_slice(&mut self, vals: &[u8]) {
        self.reserve(vals.len());
        unsafe {
            let ptr = self.as_mut_ptr().add(self.len());
            ptr.copy_from_nonoverlapping(vals.as_ptr(), vals.len());
        }
        self.len_ += vals.len() as isize;
    }

    pub fn as_ptr(&self) -> *const u8 {
        if self.is_stack() {
            let ptr: *const (*mut u8, usize) = &self.buffer;
            ptr as *const u8
        } else {
            self.buffer.0
        }
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        if self.is_stack() {
            let ptr: *mut (*mut u8, usize) = &mut self.buffer;
            ptr as *mut u8
        } else {
            self.buffer.0
        }
    }

    pub fn capacity(&self) -> usize {
        if self.is_stack() {
            size_of::<(*mut u8, usize)>()
        } else {
            self.buffer.1
        }
    }

    pub fn len(&self) -> usize {
        if self.is_stack() {
            (self.len_ - isize::MIN) as usize
        } else {
            self.len_ as usize
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_cap = self.len() + additional;

        if new_cap <= self.capacity() {
            return;
        }

        if self.is_stack() {
            // First allocation

            // Allocating heap memory.
            let layout = Layout::array::<u8>(new_cap).unwrap();
            let ptr = unsafe { std::alloc::alloc(layout) };
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            // Copy current elements
            unsafe { ptr.copy_from_nonoverlapping(self.as_ptr(), self.len()) };

            // Update the properties
            self.buffer.0 = ptr;
            self.buffer.1 = new_cap;
            self.len_ = self.len() as isize;
        } else {
            let layout = Layout::array::<u8>(self.capacity()).unwrap();
            let ptr = unsafe { std::alloc::realloc(self.as_mut_ptr(), layout, new_cap) };
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            self.buffer.0 = ptr;
            self.buffer.1 = new_cap;
        }
    }

    fn is_stack(&self) -> bool {
        self.len_ < 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let buffer = Buffer::new();
        assert_eq!(0, buffer.len());
        assert!(0 < buffer.capacity());
    }

    #[test]
    fn reserve() {
        let mut buffer = Buffer::new();
        for i in 0..40 {
            buffer.reserve(i);
            assert_eq!(0, buffer.len());
            assert!(i <= buffer.capacity());
        }
    }

    #[test]
    fn push() {
        let mut buffer = Buffer::new();
        let mut vec = Vec::new();

        for i in 0..40 {
            buffer.push(i);
            vec.push(i);

            let expected: &[u8] = vec.as_ref();
            assert_eq!(expected, buffer.as_ref());
        }
    }

    #[test]
    fn extend_from_slice() {
        let mut buffer = Buffer::new();
        let mut vec = Vec::new();

        for i in 0..40 {
            let vals = [i; 10];
            buffer.extend_from_slice(&vals);
            vec.extend_from_slice(&vals);

            let expected: &[u8] = vec.as_ref();
            assert_eq!(expected, buffer.as_ref());
        }
    }
}
