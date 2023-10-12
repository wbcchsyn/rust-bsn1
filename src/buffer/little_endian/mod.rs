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

const HEAP_FLAG: usize = 1 << (usize::BITS - 1);
const LEN_MASK: usize = !HEAP_FLAG;
const ALIGN: usize = std::mem::align_of::<u8>();

#[repr(C)]
pub struct Buffer {
    data_: *mut u8,
    cap_: usize,
    len_: usize,
}

impl Buffer {
    pub const fn new() -> Self {
        Self {
            data_: std::ptr::null_mut(),
            cap_: 0,
            len_: 0,
        }
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        if self.is_stack() {
            return;
        }

        unsafe {
            let layout = Layout::from_size_align_unchecked(self.cap_, ALIGN);
            alloc::dealloc(self.data_, layout);
        }
    }
}

impl Buffer {
    pub fn len(&self) -> usize {
        if self.is_stack() {
            self.len_ >> (usize::BITS - u8::BITS)
        } else {
            self.len_ & LEN_MASK
        }
    }

    pub fn capacity(&self) -> usize {
        if self.is_stack() {
            std::mem::size_of::<Self>() - std::mem::size_of::<u8>()
        } else {
            self.cap_
        }
    }

    pub unsafe fn set_len(&mut self, len: usize) {
        if self.is_stack() {
            const MASK: usize = (u8::MAX as usize) << (usize::BITS - u8::BITS);
            self.len_ &= !MASK;
            self.len_ |= len << (usize::BITS - u8::BITS);
        } else {
            self.len_ = len | HEAP_FLAG;
        }
    }

    pub fn as_ptr(&self) -> *const u8 {
        if self.is_stack() {
            let ptr = self as *const Self;
            ptr as *const u8
        } else {
            self.data_
        }
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        let ptr = self.as_ptr();
        ptr as *mut u8
    }

    fn is_stack(&self) -> bool {
        self.len_ & HEAP_FLAG == 0
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

#[cfg(test)]
mod tests {
    use super::Buffer;

    const MIN_CAP: usize = std::mem::size_of::<Buffer>() - std::mem::size_of::<u8>();

    #[test]
    fn new() {
        let buffer = Buffer::new();
        assert_eq!(0, buffer.len());
        assert_eq!(MIN_CAP, buffer.capacity());
    }
}
