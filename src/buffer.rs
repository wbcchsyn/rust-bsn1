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
use core::mem::size_of;
use core::ptr::null_mut;

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

impl Buffer {
    pub const fn new() -> Self {
        Self {
            len_: isize::MIN,
            buffer: (null_mut(), 0),
        }
    }
}

impl Buffer {
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
}
