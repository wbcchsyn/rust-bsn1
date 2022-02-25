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

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::mem::{align_of, size_of, size_of_val};
use core::ops::{Index, IndexMut};
use std::alloc::{self, Layout};
use std::borrow::Borrow;
use std::fmt;

#[repr(C)]
pub struct Buffer1 {
    len_: isize,
    data_: *mut u8,
    cap_: usize,
}

impl Drop for Buffer1 {
    #[inline]
    fn drop(&mut self) {
        if self.is_stack() {
            return;
        }

        unsafe {
            let layout = Layout::from_size_align_unchecked(self.capacity(), align_of::<u8>());
            alloc::dealloc(self.as_mut_ptr(), layout);
        }
    }
}

impl AsRef<[u8]> for Buffer1 {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl AsMut<[u8]> for Buffer1 {
    fn as_mut(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl fmt::Debug for Buffer1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let contents: &[u8] = self.as_ref();
        f.debug_tuple("Buffer").field(&contents).finish()
    }
}

impl Borrow<[u8]> for Buffer1 {
    fn borrow(&self) -> &[u8] {
        self.as_ref()
    }
}

impl Hash for Buffer1 {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        let this: &[u8] = self.borrow();
        this.hash(hasher);
    }
}

impl Index<usize> for Buffer1 {
    type Output = u8;
    fn index(&self, i: usize) -> &u8 {
        &self.as_ref()[i]
    }
}

impl IndexMut<usize> for Buffer1 {
    fn index_mut(&mut self, i: usize) -> &mut u8 {
        &mut self.as_mut()[i]
    }
}

impl Buffer1 {
    pub fn len(&self) -> usize {
        if 0 <= self.len_ {
            self.len_ as usize
        } else {
            (self.len_ - std::isize::MIN) as usize
        }
    }

    pub fn capacity(&self) -> usize {
        if self.is_stack() {
            (size_of_val(&self.data_) + size_of_val(&self.cap_)) / size_of::<u8>()
        } else {
            self.cap_
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        if self.is_stack() {
            let data: *const *mut u8 = &self.data_;
            let data = data as *const u8;
            data
        } else {
            self.data_
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_cap = self.len() + additional;

        if new_cap <= self.capacity() {
            return;
        }

        if self.is_stack() {
            let layout = Layout::array::<u8>(new_cap).unwrap();
            unsafe {
                let data = alloc::alloc(layout);
                if data.is_null() {
                    alloc::handle_alloc_error(layout);
                }

                data.copy_from_nonoverlapping(self.as_ptr(), self.capacity());
                self.len_ += std::isize::MIN;
                self.cap_ = new_cap;
                self.data_ = data;
            }
        } else {
            unsafe {
                let layout = Layout::from_size_align_unchecked(self.capacity(), align_of::<u8>());
                let data = alloc::realloc(self.as_mut_ptr(), layout, new_cap);
                if data.is_null() {
                    let layout = Layout::from_size_align_unchecked(new_cap, align_of::<u8>());
                    alloc::handle_alloc_error(layout);
                }
                self.data_ = data;
                self.cap_ = new_cap;
            }
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
        if self.is_stack() {
            let data: *mut *mut u8 = &mut self.data_;
            let data = data as *mut u8;
            data
        } else {
            self.data_
        }
    }

    fn is_stack(&self) -> bool {
        0 <= self.len_
    }
}

#[derive(Clone)]
pub enum Buffer {
    Heap(Vec<u8>),
    Stack(StackBuffer),
}

impl From<&[u8]> for Buffer {
    fn from(vals: &[u8]) -> Self {
        match StackBuffer::from_bytes(vals) {
            None => Buffer::Heap(Vec::from(vals)),
            Some(s) => Buffer::Stack(s),
        }
    }
}

impl Buffer {
    pub const fn new() -> Self {
        Self::Stack(StackBuffer::new())
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

        match self {
            Self::Heap(v) => v.push(val),
            Self::Stack(s) => s.push(val),
        }
    }

    #[inline]
    pub fn extend_from_slice(&mut self, vals: &[u8]) {
        self.reserve(vals.len());
        match self {
            Self::Heap(v) => v.extend_from_slice(vals),
            Self::Stack(s) => unsafe { s.extend_from_slice(vals) },
        }
    }

    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        match self {
            Self::Heap(v) => v.as_ptr(),
            Self::Stack(s) => s.as_ptr(),
        }
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        match self {
            Self::Heap(v) => v.as_mut_ptr(),
            Self::Stack(s) => s.as_mut_ptr(),
        }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        match self {
            Self::Heap(v) => v.capacity(),
            Self::Stack(s) => s.capacity(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::Heap(v) => v.len(),
            Self::Stack(s) => s.len(),
        }
    }

    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        match self {
            Self::Heap(v) => v.set_len(new_len),
            Self::Stack(s) => s.set_len(new_len),
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        match self {
            Self::Heap(v) => v.reserve(additional),
            Self::Stack(s) => {
                if s.len() + additional <= s.capacity() {
                    return;
                } else {
                    let mut v = Vec::with_capacity(s.len() + additional);
                    v.extend_from_slice(s.as_ref());
                    *self = Self::Heap(v)
                }
            }
        }
    }

    #[inline]
    pub fn into_vec(self) -> Vec<u8> {
        match self {
            Self::Heap(v) => v,
            Self::Stack(s) => Vec::from(s.as_ref()),
        }
    }
}

#[cfg(test)]
mod buffer_tests {
    use super::*;
    use core::alloc::Layout;

    #[test]
    fn size_align() {
        let layout = Layout::new::<Buffer>();
        let vec_layout = Layout::new::<Vec<u8>>();

        assert_eq!(vec_layout.align(), layout.align());
        assert_eq!(vec_layout.size() + layout.align(), layout.size());
    }

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
    // The size of 'Buffer' will be 'size_of::<Vec<u8>>() + align_of::<Vec<u8>>()'.
    const CAPACITY: usize = size_of::<Vec<u8>>() + align_of::<Vec<u8>>() - 2;
}

impl StackBuffer {
    pub const fn new() -> Self {
        Self {
            buffer: [0; Self::CAPACITY],
            len_: 0,
        }
    }

    pub fn from_bytes(vals: &[u8]) -> Option<Self> {
        if vals.len() <= Self::CAPACITY {
            let mut ret = Self::new();
            unsafe { ret.extend_from_slice(vals) };
            Some(ret)
        } else {
            None
        }
    }
}

impl AsRef<[u8]> for StackBuffer {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl Index<usize> for StackBuffer {
    type Output = u8;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            let ptr = self.as_ptr().add(index);
            &*ptr
        }
    }
}

impl IndexMut<usize> for StackBuffer {
    #[inline]
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
    #[inline]
    pub unsafe fn push(&mut self, val: u8) {
        debug_assert!(self.len() < self.capacity());

        self.buffer[self.len()] = val;
        self.len_ += 1;
    }

    /// # Safety
    ///
    /// The behavior is undefined if the length will exceeds the capacity.
    #[inline]
    pub unsafe fn extend_from_slice(&mut self, vals: &[u8]) {
        debug_assert!(self.len() + vals.len() <= self.capacity());

        let ptr = self.as_mut_ptr().add(self.len());
        ptr.copy_from_nonoverlapping(vals.as_ptr(), vals.len());
        self.len_ += vals.len() as u8;
    }

    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.buffer.as_ptr()
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.buffer.as_mut_ptr()
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len_ as usize
    }

    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        self.len_ = new_len as u8
    }

    #[inline]
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

    #[test]
    fn extend_from_slice() {
        let mut buffer = StackBuffer::new();
        let mut v = Vec::new();

        for i in 0..(StackBuffer::CAPACITY / 2) {
            let bytes: &[u8] = &[i as u8, i as u8];
            v.extend_from_slice(bytes);
            unsafe { buffer.extend_from_slice(bytes) };
            assert_eq!(v.as_ref() as &[u8], buffer.as_ref());
        }
    }
}
