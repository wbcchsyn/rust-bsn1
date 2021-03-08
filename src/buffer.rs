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
use core::ops::{Index, IndexMut};
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
    #[inline]
    fn as_ref(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl AsMut<[u8]> for Buffer {
    #[inline]
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
    #[inline]
    fn borrow(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl Hash for Buffer {
    #[inline]
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        let this: &[u8] = self.borrow();
        this.hash(hasher);
    }
}

impl Index<usize> for Buffer {
    type Output = u8;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            let ptr = self.as_ptr().add(index);
            &*ptr
        }
    }
}

impl IndexMut<usize> for Buffer {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe {
            let ptr = self.as_mut_ptr().add(index);
            &mut *ptr
        }
    }
}

impl<T> PartialEq<T> for Buffer
where
    T: Borrow<[u8]>,
{
    #[inline]
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
    #[inline]
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        let this: &[u8] = self.borrow();
        let other: &[u8] = other.borrow();
        this.partial_cmp(other)
    }
}

impl Ord for Buffer {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let this: &[u8] = self.borrow();
        let other: &[u8] = other.borrow();
        this.cmp(other)
    }
}

impl Buffer {
    /// # Safety
    ///
    /// The behavior is undefined if the length will exceeds the capacity.
    #[inline]
    pub unsafe fn push(&mut self, val: u8) {
        debug_assert!(self.len() < self.capacity());

        let ptr = self.as_mut_ptr().add(self.len());
        *ptr = val;
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

    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        if self.is_stack() {
            let ptr: *const (*mut u8, usize) = &self.buffer;
            ptr as *const u8
        } else {
            self.buffer.0
        }
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        if self.is_stack() {
            let ptr: *mut (*mut u8, usize) = &mut self.buffer;
            ptr as *mut u8
        } else {
            self.buffer.0
        }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        if self.is_stack() {
            size_of::<(*mut u8, usize)>()
        } else {
            self.buffer.1
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        if self.is_stack() {
            (self.len_ - isize::MIN) as usize
        } else {
            self.len_ as usize
        }
    }

    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        if self.is_stack() {
            self.len_ = isize::MIN + new_len as isize;
        } else {
            self.len_ = new_len as isize;
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

    #[inline]
    fn is_stack(&self) -> bool {
        self.len_ < 0
    }
}

#[cfg(test)]
mod buffer_tests {
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
        const LENGTH: usize = 40;

        let mut buffer = Buffer::with_capacity(LENGTH);
        let mut vec = Vec::new();

        for i in 0..LENGTH {
            unsafe { buffer.push(i as u8) };
            vec.push(i as u8);

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

#[derive(Clone, Copy)]
pub struct StackBuffer {
    buffer: [u8; Self::CAPACITY],
    len_: u8,
}

impl StackBuffer {
    const CAPACITY: usize = size_of::<i128>();
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
    fn as_ref(&self) -> &[u8] {
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
