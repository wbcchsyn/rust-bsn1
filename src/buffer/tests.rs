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

//! This module provides a tests for `Buffer`.
//! Both `buffer::little_endian::Buffer` and `buffer::universal_endian::Buffer`
//! use this file in common.

use super::*;
use std::iter::FromIterator;
const INIT_CAPACITY: usize = endian::INIT_CAPACITY;

#[test]
fn new() {
    let buffer = Buffer::new();
    assert_eq!(0, buffer.len());
    assert_eq!(INIT_CAPACITY, buffer.capacity());
}

#[test]
fn with_capacity() {
    for i in 0..100 {
        let buffer = Buffer::with_capacity(i);
        assert_eq!(0, buffer.len());
        assert_eq!(INIT_CAPACITY.max(i), buffer.capacity());
    }
}

#[test]
fn reserve() {
    for i in 0..40 {
        let mut buffer = Buffer::new();
        buffer.reserve(i);

        assert_eq!(0, buffer.len());
        assert_eq!(INIT_CAPACITY.max(i), buffer.capacity());
    }

    for i in 0..40 {
        let v = vec![1];
        let mut buffer = Buffer::from(&v as &[u8]);

        buffer.reserve(i);
        assert_eq!(&v, buffer.as_slice());
        assert_eq!(INIT_CAPACITY.max(i + v.len()), buffer.capacity());
    }

    for i in 0..40 {
        let v = Vec::from_iter(0..200);
        let mut buffer = Buffer::from(&v as &[u8]);

        buffer.reserve(i);
        assert_eq!(&v, buffer.as_slice());
        assert_eq!(INIT_CAPACITY.max(i + v.len()), buffer.capacity());
    }
}

#[test]
fn push() {
    for i in 0..INIT_CAPACITY {
        let v = Vec::from_iter(0..i as u8);
        let mut buffer = Buffer::new();

        v.iter().for_each(|&c| unsafe { buffer.push(c) });
        assert_eq!(&v, buffer.as_slice());
        assert_eq!(INIT_CAPACITY, buffer.capacity());
    }

    for i in 0..100 {
        let v = Vec::from_iter(0..i);
        let mut buffer = Buffer::with_capacity(v.len());

        v.iter().for_each(|&c| unsafe { buffer.push(c) });
        assert_eq!(&v, buffer.as_slice());
        assert_eq!(INIT_CAPACITY.max(v.len()), buffer.capacity());
    }
}

#[test]
fn extend_from_slice() {
    let mut buffer = Buffer::new();
    let mut vec = Vec::new();

    for i in 0..40 {
        let vals = [i; 10];
        buffer.reserve(10);
        unsafe { buffer.extend_from_slice(&vals) };
        vec.extend_from_slice(&vals);

        assert_eq!(&vec, buffer.as_slice());
    }
}

#[test]
fn from_empty_vec() {
    let vals = Vec::new();
    let buffer = Buffer::from(vals);
    assert_eq!(buffer.len(), 0);
    assert_eq!(buffer.capacity(), INIT_CAPACITY);
}

#[test]
fn from_capacity_vec() {
    for i in 1..100 {
        let vals = Vec::with_capacity(i);
        let cap = vals.capacity();
        let buffer = Buffer::from(vals);

        assert_eq!(buffer.len(), 0);
        assert_eq!(cap, buffer.capacity());
    }
}

#[test]
fn from_filled_vec() {
    for i in 1..=u8::MAX {
        let vals = Vec::from_iter(0..i);
        let cap = vals.capacity();
        let buffer = Buffer::from(vals);

        assert_eq!(Vec::from_iter(0..i), buffer.as_slice());
        assert_eq!(cap, buffer.capacity());
    }
}

#[test]
fn into_vec() {
    for i in 1..=u8::MAX {
        let vec = Vec::from_iter(0..i);
        let buffer = Buffer::from(&vec[..]);
        assert_eq!(vec, buffer.into_vec());
    }
}
