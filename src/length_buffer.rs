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

use crate::Length;
use std::ops::{Deref, DerefMut};
use std::ops::{Index, IndexMut};

#[derive(Clone, Copy)]
pub struct LengthBuffer {
    buffer: [u8; Self::CAPACITY],
    len_: u8,
}

impl LengthBuffer {
    const CAPACITY: usize = Length::Definite(std::usize::MAX).len();

    pub const fn new() -> Self {
        Self {
            buffer: [0; Self::CAPACITY],
            len_: 0,
        }
    }

    /// # Safety
    ///
    /// The behaviour is undefined if the length will exceeds the capacity.
    pub unsafe fn push(&mut self, val: u8) {
        debug_assert!(self.len() < self.capacity());

        self.buffer[self.len()] = val;
        self.len_ += 1;
    }

    pub const fn as_ptr(&self) -> *const u8 {
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

    #[cfg(test)]
    pub fn as_bytes(&self) -> &[u8] {
        self
    }
}

impl Deref for LengthBuffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl DerefMut for LengthBuffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl Index<usize> for LengthBuffer {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.deref().index(index)
    }
}

impl IndexMut<usize> for LengthBuffer {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.deref_mut().index_mut(index)
    }
}

#[cfg(test)]
mod stack_buffer_tests {
    use super::*;

    #[test]
    fn new() {
        let buffer = LengthBuffer::new();
        assert_eq!(0, buffer.len());
    }

    #[test]
    fn push() {
        let mut buffer = LengthBuffer::new();
        let mut v = Vec::new();

        for i in 0..LengthBuffer::CAPACITY {
            assert_eq!(i, buffer.len());

            unsafe { buffer.push(i as u8) };
            v.push(i as u8);

            assert_eq!(&v, buffer.as_bytes());
        }

        assert_eq!(buffer.capacity(), buffer.len());
    }
}
