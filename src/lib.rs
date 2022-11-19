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

#![deny(missing_docs)]

//! `bsn1` is a rust library to serialize/deserialize in 'ASN.1' format.
//!
//! Unlike to other crates, `bsn.1` is able to treat class 'Application', 'Context-specific',
//! and 'Private' as well as 'Universal'.
//!
//! # What is ASN.1?
//!
//! ASN.1 stands for 'Abstract Syntax Notation One' and X.690 is an 'ITU-T' standard specifying
//! the following ASN.1 encoding formats.
//!
//! - Basic Encoding Rules (BER)
//! - Canonical Encoding Rules (CER)
//! - Distinguished Encoding Rules (DER)
//!
//! This crate supports BER and DER for now.
//!
//! ASN.1 resembles 'JSON' in some ways because they both are about serializing structured data,
//! however, they differ in the following points.
//!
//! - JSON is easy for a human to read, on the other hand, ASN.1 is readable for a computer.
//!   i.e. ASN.1 consumes less computer resource like CPU time than JSON does.
//! - There are 4 classes in ASN.1 formats, 'Universal', 'Application', 'Context-specific',
//!   and 'Private'.
//!   Class 'Universal' defines types like 'Integer', 'Boolean', 'String', 'Sequence' and so on
//!   like JSON. What is more, ASN.1 allows users to define a new data type using other classes.
//!
//! ASN.1 has been used all over the world for a long time and it is very stable. For example,
//! 'Transport Layer Security (TLS, SSL)', 'Lightweight Directory Access Protocol (LDAP)',
//! '4th Generation Mobile Communication System (4G)', and so on.
//!
//! See ['X.690 (07/2002)'] for details.
//!
//! ['X.690 (07/2002)']: https://www.itu.int/ITU-T/studygroups/com17/languages/X.690-0207.pdf

mod ber;
mod buffer;
mod contents;
mod contents_ref;
mod der;
mod identifier;
mod length;
mod stack_buffer;

pub use ber::{Ber, BerRef};
use buffer::Buffer;
pub use contents::Contents;
pub use contents_ref::ContentsRef;
pub use der::{Der, DerRef};
pub use identifier::{ClassTag, Id, IdRef, PCTag};
pub use length::Length;
use stack_buffer::StackBuffer;
use std::fmt;

/// Errors for this crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error {
    /// The bytes finishes before the last octet.
    UnTerminatedBytes,
    /// The bytes includes some redundant octet(s).
    /// ('ASN.1' does not allow such bytes.)
    RedundantBytes,
    /// Over flow is occurred to parse bytes as a number.
    OverFlow,
    /// 'Indefinite length' used in DER or CER.
    /// (It is only for BER, but not for DER, nor for CER.)
    IndefiniteLength,
    /// The contents of 'EOC' of the 'Indefinite Length BER' must be empty.
    BadEoc,
    /// The contents includes some invalid octet(s).
    InvalidContents,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnTerminatedBytes => f.write_str("The bytes finishes before the last octet."),
            Self::RedundantBytes => f.write_str("The bytes includes some redundant octet(s)."),
            Self::OverFlow => f.write_str("Over flow is occurred to parse bytes as a number."),
            Self::IndefiniteLength => f.write_str("'Indefinite Length' in DER or CER"),
            Self::BadEoc => f.write_str("'Indefinite Length BER' includes bad 'EOC.'"),
            Self::InvalidContents => f.write_str("Contents includes invlid octet(s)."),
        }
    }
}

impl std::error::Error for Error {}
