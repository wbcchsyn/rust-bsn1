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

use std::alloc::{self, Layout};
use std::borrow::Borrow;
use std::fmt;

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

    pub fn from_raw_parts(data: *mut u8, capacity: usize) -> Self {
        Self {
            data_: data,
            cap_: capacity,
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

const HEAP_FLAG: usize = 1 << (usize::BITS - 1);
const LEN_MASK: usize = !HEAP_FLAG;
pub const INIT_CAPACITY: usize = StackBuffer::capacity();

pub struct Buffer {
    len_: usize,
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
        let mut ret = Self::with_capacity(self.len());
        unsafe { ret.extend_from_slice(self.as_slice()) };
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
                len_: 0 | HEAP_FLAG,
                buffer_: BufferWithoutLength {
                    heap: ManuallyDrop::new(HeapBuffer::new(capacity)),
                },
            }
        }
    }

    pub fn from_vec(mut vals: Vec<u8>) -> Self {
        if vals.capacity() == 0 {
            return Self::new();
        } else {
            let buffer = HeapBuffer::from_raw_parts(vals.as_mut_ptr(), vals.capacity());
            let len_ = vals.len() | HEAP_FLAG;

            std::mem::forget(vals);

            Self {
                len_,
                buffer_: BufferWithoutLength {
                    heap: ManuallyDrop::new(buffer),
                },
            }
        }
    }

    /// # Safety
    ///
    /// The behaviour is undefined if the length will exceeds the capacity.
    pub unsafe fn push(&mut self, v: u8) {
        let old_len = self.len();

        debug_assert!(old_len < self.capacity());
        self.set_len(old_len + 1);
        self.as_mut_slice()[old_len] = v;
    }

    /// # Safety
    ///
    /// The behaviour is undefined if the length will exceeds the capacity.
    pub unsafe fn extend_from_slice(&mut self, vals: &[u8]) {
        let ptr = self.as_mut_ptr().add(self.len());
        ptr.copy_from_nonoverlapping(vals.as_ptr(), vals.len());
        self.set_len(self.len() + vals.len());
    }

    pub const fn len(&self) -> usize {
        self.len_ & LEN_MASK
    }

    pub fn capacity(&self) -> usize {
        if self.is_stack() {
            INIT_CAPACITY
        } else {
            unsafe { self.buffer_.heap.capacity() }
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
            self.len_ |= HEAP_FLAG;
        } else {
            unsafe { (&mut *self.buffer_.heap).realloc(new_cap) };
        }
    }

    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());
        self.len_ &= HEAP_FLAG;
        self.len_ |= new_len;
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

    const fn is_stack(&self) -> bool {
        self.len_ & HEAP_FLAG == 0
    }

    pub fn into_vec(mut self) -> Vec<u8> {
        if self.is_stack() {
            Vec::from(self.as_slice())
        } else {
            unsafe {
                let ret = Vec::from_raw_parts(self.as_mut_ptr(), self.len(), self.capacity());
                std::mem::forget(self);
                ret
            }
        }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl fmt::Debug for Buffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let contents: &[u8] = self.as_slice();
        f.debug_tuple("Buffer").field(&contents).finish()
    }
}

impl Borrow<[u8]> for Buffer {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<T> PartialEq<T> for Buffer
where
    T: Borrow<[u8]>,
{
    fn eq(&self, other: &T) -> bool {
        self.as_slice() == other.borrow()
    }
}

impl Eq for Buffer {}
