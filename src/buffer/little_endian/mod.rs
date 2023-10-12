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

const HEAP_FLAG: usize = 1 << (usize::BITS - 1);
const LEN_MASK: usize = !HEAP_FLAG;

#[repr(C)]
pub struct Buffer {
    data_: *mut u8,
    cap_: usize,
    len_: usize,
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
}
