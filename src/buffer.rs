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

use std::alloc::{self, Layout};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut, Index, IndexMut};

struct HeapBuffer {
    data_: *mut u8,
    cap_: usize,
}

impl Drop for HeapBuffer {
    fn drop(&mut self) {
        unsafe {
            let layout = Layout::from_size_align_unchecked(self.cap_, std::mem::align_of::<u8>());
            alloc::dealloc(self.data_, layout);
        }
    }
}

impl HeapBuffer {
    pub fn new(capacity: usize) -> Self {
        debug_assert!(0 < capacity);

        let layout = Layout::array::<u8>(capacity).unwrap();
        unsafe {
            let data = alloc::alloc(layout);
            if data.is_null() {
                alloc::handle_alloc_error(layout);
            }

            Self {
                data_: data,
                cap_: capacity,
            }
        }
    }

    pub fn capacity(&self) -> usize {
        self.cap_
    }

    pub fn realloc(&mut self, new_capacity: usize) {
        let layout = Layout::array::<u8>(self.capacity()).unwrap();
        unsafe {
            let data = alloc::realloc(self.data_, layout, new_capacity);
            if data.is_null() {
                let layout = Layout::array::<u8>(new_capacity).unwrap();
                alloc::handle_alloc_error(layout);
            }

            self.data_ = data;
            self.cap_ = new_capacity;
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.data_
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.data_
    }
}

struct StackBuffer {
    data_: [u8; std::mem::size_of::<HeapBuffer>()],
}

impl StackBuffer {
    pub const fn capacity() -> usize {
        std::mem::size_of::<Self>()
    }

    pub const fn new() -> Self {
        Self {
            data_: [0; Self::capacity()],
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.data_.as_ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.data_.as_mut_ptr()
    }
}

use std::mem::ManuallyDrop;

union BufferWithoutLength {
    stack: ManuallyDrop<StackBuffer>,
    heap: ManuallyDrop<HeapBuffer>,
}

impl Drop for BufferWithoutLength {
    // `self` cannot know which field is used.
    // The owner of this union must drop the field.
    fn drop(&mut self) {}
}

#[repr(C)]
pub struct Buffer {
    len_: isize,
    buffer_: BufferWithoutLength,
}

unsafe impl Send for Buffer {}
unsafe impl Sync for Buffer {}

impl Drop for Buffer {
    fn drop(&mut self) {
        if self.is_stack() {
            unsafe {
                ManuallyDrop::drop(&mut self.buffer_.stack);
            }
        } else {
            unsafe {
                ManuallyDrop::drop(&mut self.buffer_.heap);
            }
        }
    }
}

impl Clone for Buffer {
    fn clone(&self) -> Self {
        Self::from(self.as_bytes())
    }
}

impl From<&[u8]> for Buffer {
    fn from(vals: &[u8]) -> Self {
        let mut ret = Self::with_capacity(vals.len());
        ret.extend_from_slice(vals);
        ret
    }
}

impl Buffer {
    pub const fn new() -> Self {
        Self {
            len_: 0,
            buffer_: BufferWithoutLength {
                stack: ManuallyDrop::new(StackBuffer::new()),
            },
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= StackBuffer::capacity() {
            Self::new()
        } else {
            Self {
                len_: std::isize::MIN,
                buffer_: BufferWithoutLength {
                    heap: ManuallyDrop::new(HeapBuffer::new(capacity)),
                },
            }
        }
    }
}

impl fmt::Debug for Buffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let contents: &[u8] = self;
        f.debug_tuple("Buffer").field(&contents).finish()
    }
}

impl Deref for Buffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl DerefMut for Buffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl Borrow<[u8]> for Buffer {
    fn borrow(&self) -> &[u8] {
        self.deref()
    }
}

impl Hash for Buffer {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        let this: &[u8] = self;
        this.hash(hasher);
    }
}

impl Index<usize> for Buffer {
    type Output = u8;
    fn index(&self, i: usize) -> &u8 {
        &self.as_bytes()[i]
    }
}

impl IndexMut<usize> for Buffer {
    fn index_mut(&mut self, i: usize) -> &mut u8 {
        &mut self.as_mut_bytes()[i]
    }
}

impl<T> PartialEq<T> for Buffer
where
    T: Borrow<[u8]>,
{
    fn eq(&self, other: &T) -> bool {
        self.deref() == other.borrow()
    }
}

impl Eq for Buffer {}

impl<T> PartialOrd<T> for Buffer
where
    T: Borrow<[u8]>,
{
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        self.deref().partial_cmp(other.borrow())
    }
}

impl Ord for Buffer {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}

impl Buffer {
    /// # Safety
    ///
    /// The behaviour is undefined if the length will exceeds the capacity.
    pub unsafe fn push(&mut self, v: u8) {
        let old_len = self.len();

        debug_assert!(old_len < self.capacity());
        self.set_len(old_len + 1);
        self.as_mut_bytes()[old_len] = v;
    }

    pub fn extend_from_slice(&mut self, vals: &[u8]) {
        self.reserve(vals.len());
        unsafe {
            let ptr = self.as_mut_ptr().add(self.len());
            ptr.copy_from_nonoverlapping(vals.as_ptr(), vals.len());
            self.set_len(self.len() + vals.len());
        }
    }

    pub fn len(&self) -> usize {
        if 0 <= self.len_ {
            self.len_ as usize
        } else {
            (self.len_ - std::isize::MIN) as usize
        }
    }

    pub fn capacity(&self) -> usize {
        if self.is_stack() {
            StackBuffer::capacity()
        } else {
            unsafe { (&*self.buffer_.heap).capacity() }
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        unsafe {
            if self.is_stack() {
                self.buffer_.stack.as_ptr()
            } else {
                self.buffer_.heap.as_ptr()
            }
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_cap = self.len() + additional;

        if new_cap <= self.capacity() {
            return;
        }

        if self.is_stack() {
            let mut heap = HeapBuffer::new(new_cap);
            unsafe {
                heap.as_mut_ptr()
                    .copy_from_nonoverlapping(self.as_ptr(), self.len());
            }
            self.buffer_.heap = ManuallyDrop::new(heap);
            self.len_ += std::isize::MIN;
        } else {
            unsafe { (&mut *self.buffer_.heap).realloc(new_cap) };
        }
    }

    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());
        if self.is_stack() {
            self.len_ = new_len as isize;
        } else {
            self.len_ = std::isize::MIN + new_len as isize
        }
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        unsafe {
            if self.is_stack() {
                (&mut *self.buffer_.stack).as_mut_ptr()
            } else {
                (&mut *self.buffer_.heap).as_mut_ptr()
            }
        }
    }

    fn is_stack(&self) -> bool {
        0 <= self.len_
    }

    pub fn into_vec(mut self) -> Vec<u8> {
        if self.is_stack() {
            Vec::from(self.as_bytes())
        } else {
            unsafe {
                let ret = Vec::from_raw_parts(self.as_mut_ptr(), self.len(), self.capacity());
                std::mem::forget(self);
                ret
            }
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        self
    }

    pub fn as_mut_bytes(&mut self) -> &mut [u8] {
        self
    }
}

#[cfg(test)]
mod buffer_tests {
    use super::*;
    use std::iter::FromIterator;

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

        let v = vec![1];
        let mut buffer = Buffer::from(&v as &[u8]);
        for i in 0..40 {
            buffer.reserve(i);
            assert_eq!(&v, buffer.as_bytes());
            assert!(i <= buffer.capacity());
        }

        let v = Vec::from_iter(0..200);
        let mut buffer = Buffer::from(&v as &[u8]);
        for i in 0..40 {
            buffer.reserve(i);
            assert_eq!(&v, buffer.as_bytes());
            assert!(i <= buffer.capacity());
        }
    }

    #[test]
    fn push() {
        for i in 0..Buffer::new().capacity() {
            let v = Vec::from_iter(0..i as u8);

            let mut buffer = Buffer::new();
            for &c in v.iter() {
                unsafe { buffer.push(c) };
            }

            assert_eq!(&v, buffer.as_bytes());
        }

        for i in 0..100 {
            let v = Vec::from_iter(0..i);
            let mut buffer = Buffer::with_capacity(v.len());
            for &c in v.iter() {
                unsafe { buffer.push(c) };
            }

            assert_eq!(&v, buffer.as_bytes());
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

            assert_eq!(&vec, buffer.as_bytes());
        }
    }
}
