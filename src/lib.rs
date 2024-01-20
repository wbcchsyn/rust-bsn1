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

#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

mod ber;
mod ber_ref;
mod buffer;
mod contents;
mod contents_ref;
mod der;
mod der_ref;
mod id_tags;
mod identifier;
mod identifier_ref;
mod length;
mod length_buffer;
mod misc;

pub use ber::Ber;
pub use ber_ref::BerRef;
pub use buffer::Buffer;
pub use contents::Contents;
pub use contents_ref::ContentsRef;
pub use der::Der;
pub use der_ref::DerRef;
pub use id_tags::{ClassTag, PCTag, TagNumber};
pub use identifier::Id;
pub use identifier_ref::IdRef;
pub use length::Length;
use length_buffer::LengthBuffer;
use std::fmt;

/// Errors for this crate.
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    /// The bytes finish before the last octet.
    UnTerminatedBytes,
    /// The bytes include some redundant octet(s).
    /// ('ASN.1' does not allow such bytes.)
    RedundantBytes,
    /// Over flow is occurred to parse bytes as a number.
    OverFlow,
    /// 'Indefinite length' is used where not allowed.
    /// (It is only for BER of some type, but not for DER, nor for CER.)
    IndefiniteLength,
    /// The contents of 'EOC' of the 'Indefinite Length BER' must be empty.
    BadEoc,
    /// The contents include invalid octet(s).
    InvalidContents,
    /// The identifier does not match to that of data type when deserialized.
    UnmatchedId,
    /// Invarid as UTF-8.
    InvalidUtf8,
    /// The key-value pair is invalid.
    InvalidKeyValuePair,
    /// IO Error for serialization/deserialization.
    ///
    /// Note that this error cannot be compared with others.
    /// `PartialEq::eq` always returns `false` for this error.
    Io(std::io::Error),
    /// Wrapper of [`std::error::Error`].
    ///
    /// This is used when users want to use their own error type.
    ///
    /// Note that this error cannot be compared with others.
    /// `PartialEq::eq` always returns `false` for this error.
    Boxed(Box<dyn std::error::Error>),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnTerminatedBytes => f.write_str("The bytes finish before the last octet."),
            Self::RedundantBytes => f.write_str("The bytes include some redundant octet(s)."),
            Self::OverFlow => f.write_str("Over flow is occurred to parse bytes as a number."),
            Self::IndefiniteLength => f.write_str("'Indefinite Length' is used where not allowed."),
            Self::BadEoc => f.write_str("'Indefinite Length BER' includes a bad 'EOC.'"),
            Self::InvalidContents => f.write_str("Contents include invlid octet(s)."),
            Self::UnmatchedId => f.write_str("The identifier does not match to that of data type."),
            Self::InvalidUtf8 => f.write_str("Invalid as UTF-8."),
            Self::InvalidKeyValuePair => f.write_str("The key-value pair is invalid."),
            Self::Io(err) => err.fmt(f),
            Self::Boxed(err) => err.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::UnTerminatedBytes => matches!(other, Self::UnTerminatedBytes),
            Self::RedundantBytes => matches!(other, Self::RedundantBytes),
            Self::OverFlow => matches!(other, Self::OverFlow),
            Self::IndefiniteLength => matches!(other, Self::IndefiniteLength),
            Self::BadEoc => matches!(other, Self::BadEoc),
            Self::InvalidContents => matches!(other, Self::InvalidContents),
            Self::UnmatchedId => matches!(other, Self::UnmatchedId),
            Self::InvalidUtf8 => matches!(other, Self::InvalidUtf8),
            Self::InvalidKeyValuePair => matches!(other, Self::InvalidKeyValuePair),
            Self::Io(_) => false,
            Self::Boxed(_) => false,
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Self::Io(err)
    }
}
