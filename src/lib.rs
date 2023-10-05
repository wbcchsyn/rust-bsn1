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

//! `bsn1` is a rust library to serialize/deserialize in 'ASN.1' format.
//!
//! # What is ASN.1?
//!
//! ASN.1 stands for 'Abstract Syntax Notation One' and X.690 is an 'ITU-T' standard specifying
//! the following ASN.1 encoding format.
//!
//! - Basic Encoding Rules (BER)
//! - Canonical Encoding Rules (CER)
//! - Distinguished Encoding Rules (DER)
//!
//! This crate supports BER and DER for now.
//!
//! ASN.1 resembles 'JSON' in some ways because they both are standard serializing structured data,
//! however, they differ in the following points.
//!
//! - JSON is easy for a person to read, on the other hand, ASN.1 is readable for a computer.
//!   i.e. ASN.1 consumes less computer resources (e.g. CPU time) than JSON does.
//! - There are 4 classes in ASN.1 formats, 'Universal', 'Application', 'Context-specific',
//!   and 'Private'.
//!   Class 'Universal' defines types like 'Integer', 'Boolean', 'String', 'Sequence' and so on
//!   like JSON. What is more, ASN.1 allows users to define a new data type using another class.
//!
//! ASN.1 has been used all over the world for a long time and it is very stable. For example,
//! 'Transport Layer Security (TLS, SSL)', 'Lightweight Directory Access Protocol (LDAP)',
//! '4th Generation Mobile Communication System (4G)', and so on.
//!
//! See also [X.690 (07/2002)] and [Wikipedia].
//!
//! [X.690 (07/2002)]: https://www.itu.int/ITU-T/studygroups/com17/languages/X.690-0207.pdf
//! [Wikipedia]: https://en.wikipedia.org/wiki/X.690
//!
//! # Examples
//!
//! 'Lightweight Directory Access Protocol (LDAP)' adopts BER.
//! Let's make/parse LDAP Bind Operation (i.e. Login Query.)
//!
//! See [RFC4511](https://www.rfc-editor.org/rfc/rfc4511) for the details.
//!
//! ```
//! use bsn1::{Ber, BerRef, ContentsRef, Id, IdRef, ClassTag, PCTag};
//!
//! /// Creates a BindRequest from `name` and `password`.
//! ///
//! /// BindRequest ::= [APPLICATION 0] SEQUENCE {
//! ///          version INTEGER (1 .. 127),
//! ///          name LDAPDN,
//! ///          authentication AuthenticationChoice }
//! fn new_bind_request(name: &str, password: &[u8]) -> Ber {
//!     // BindRequest is constituted of version, name, and authentication.
//!     // '[APPLICATION 0] SEQUENCE' means "a sequence, but the class is APPLICATION, and the
//!     // number is 0."
//!     // The RFC does not refer to the Primitive/Constructed flag,
//!     // but SEQUENCE is usually Constructed.
//!     const ID_NUMBER: u32 = 0;
//!     let id = Id::new(ClassTag::Application, PCTag::Constructed, ID_NUMBER);
//!
//!     let contents = [new_bind_version(), new_bind_name(name),
//!                     new_bind_authentication(password)];
//!
//!     Ber::from_id_iterator(&id, contents.iter())
//! }
//!
//! /// Creates a `version` for bind request.
//! /// This function always returns 3 (the current latest version.)
//! fn new_bind_version() -> Ber {
//!     Ber::from(3_i32)
//! }
//!
//! /// Creates a `name` for bind request from `name`.
//! ///
//! /// LDAPDN ::= LDAPString
//! ///            -- Constrained to <distinguishedName> [RFC4514]
//! ///
//! /// LDAPString ::= OCTET STRING -- UTF-8 encoded,
//! ///                             -- [ISO10646] characters
//! fn new_bind_name(name: &str) -> Ber {
//!     // BER allows both Primitive and Constructed for OCTET STRING.
//!     // This function returns Primitive BER.
//!     // Call octet_string_constructed() instead if you prefer Constructed.
//!     Ber::octet_string(name.as_bytes())
//! }
//!
//! /// Creates a `simple authentication` for bind request from `password`.
//! ///
//! /// AuthenticationChoice ::= CHOICE {
//! ///      simple                  [0] OCTET STRING,
//! ///      -- 1 and 2 reserved
//! ///      sasl                    [3] SaslCredentials,
//! ///      ... }
//! fn new_bind_authentication(password: &[u8]) -> Ber {
//!    // 'AuthenticationChoice' is either 'simple [0] OCTET STRING' or 'sasl [3] SaslCredentials'.
//!    // This function selects 'simple'.
//!    //
//!    // '[0] OCTET STRING' means "OCTET STRING, but the number is 0."
//!    // RFC does not refer to the class and Primitive/Constructed flag.
//!    // This function returns ContextSpecific and Primitive BER.
//!    const ID_NUMBER: u32 = 0;
//!    let id = Id::new(ClassTag::ContextSpecific, PCTag::Primitive, ID_NUMBER);
//!
//!    let contents = <&ContentsRef>::from(password);
//!
//!    Ber::new(&id, contents)
//! }
//!
//! /// Tries to parse bind request and returns `(name, password)`.
//! fn parse_bind_request(req: &[u8]) -> Result<(&str, &[u8]), String> {
//!     let req = BerRef::parse(req)
//!                 .map_err(|e| format!("Failed to parse the request as a BER: {}", e))?;
//!
//!     let id = req.id();
//!     if id.class() != ClassTag::Application || id.number() != Ok(0) {
//!         return Err("The id of the request is bad.".to_string());
//!     }
//!
//!     let bytes = req.contents().as_bytes();
//!     let version_ber = BerRef::parse(bytes)
//!                         .map_err(|e| format!("Failed to parse the request version: {}", e))?;
//!     let version = parse_bind_version(version_ber)?;
//!     if version != 3 {
//!         return Err("This function supports only version 3.".to_string());
//!     }
//!
//!     let bytes = &bytes[version_ber.as_bytes().len()..];
//!     let name_ber = BerRef::parse(bytes)
//!                      .map_err(|e| format!("Failed to parse the request name: {}", e))?;
//!     let name = parse_bind_name(name_ber)?;
//!
//!     let bytes = &bytes[name_ber.as_bytes().len()..];
//!     let auth_ber = BerRef::parse(bytes)
//!                      .map_err(|e|
//!                               format!("Failed to parse the request authentication: {}", e))?;
//!     let password = parse_bind_authentication(auth_ber)?;
//!
//!     let bytes = &bytes[auth_ber.as_bytes().len()..];
//!     if bytes.is_empty() == false {
//!         return Err("There are some bad octets at the end of the request.".to_string());
//!     }
//!
//!     Ok((name, password))
//! }
//!
//! /// Tries to parse the version of bind request.
//! fn parse_bind_version(version: &BerRef) -> Result<i32, String> {
//!     if version.id() != IdRef::integer() {
//!         Err("The id of the version is bad.".to_string())
//!     } else {
//!         version.contents()
//!                .to_integer()
//!                .map_err(|e| format!("Failed to parse the version: {}", e))
//!     }
//! }
//!
//! /// Tries to parse the name of bind request.
//! fn parse_bind_name(name: &BerRef) -> Result<&str, String> {
//!     if name.id() != IdRef::octet_string() && name.id() != IdRef::octet_string_constructed() {
//!         Err("The id of the name is bad.".to_string())
//!     } else {
//!         let contents = name.contents().as_bytes();
//!         std::str::from_utf8(contents).map_err(|e| format!("Failed to parse the name: {}", e))
//!     }
//! }
//!
//! /// Tries to parse the password of bind request.
//! fn parse_bind_authentication(authentication: &BerRef) -> Result<&[u8], String> {
//!     let id = authentication.id();
//!     if id.number() == Ok(3) {
//!         Err("This function supports only simple authentication".to_string())
//!     } else if id.number() != Ok(0) {
//!         Err("The id of the authentication is bad".to_string())
//!     } else {
//!         Ok(authentication.contents().as_bytes())
//!     }
//! }
//!
//! // Create a bind request
//! let name = "uid=user,dc=my_company,dc=co,dc=jp";
//! let password = "open_sesami".as_bytes();
//! let request = new_bind_request(name, password);
//!
//! // The client will send the byte to the server actually.
//! let bytes = request.as_bytes();
//!
//! // The LDAP server will parse the request.
//! let (name_, password_) = parse_bind_request(bytes).unwrap();
//!
//! assert_eq!(name, name_);
//! assert_eq!(password, password_);
//! ```

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

pub use ber::Ber;
pub use ber_ref::BerRef;
use buffer::Buffer;
pub use contents::Contents;
pub use contents_ref::ContentsRef;
pub use der::Der;
pub use der_ref::DerRef;
pub use id_tags::{ClassTag, PCTag};
pub use identifier::Id;
pub use identifier_ref::IdRef;
pub use length::Length;
use length_buffer::LengthBuffer;
use std::fmt;

/// Errors for this crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error {
    /// The bytes finish before the last octet.
    UnTerminatedBytes,
    /// The bytes include some redundant octet(s).
    /// ('ASN.1' does not allow such bytes.)
    RedundantBytes,
    /// Over flow is occurred to parse bytes as a number.
    OverFlow,
    /// 'Indefinite length' used in DER or CER.
    /// (It is only for BER, but not for DER, nor for CER.)
    IndefiniteLength,
    /// The contents of 'EOC' of the 'Indefinite Length BER' must be empty.
    BadEoc,
    /// The contents include invalid octet(s).
    InvalidContents,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnTerminatedBytes => f.write_str("The bytes finish before the last octet."),
            Self::RedundantBytes => f.write_str("The bytes include some redundant octet(s)."),
            Self::OverFlow => f.write_str("Over flow is occurred to parse bytes as a number."),
            Self::IndefiniteLength => f.write_str("'Indefinite Length' in DER or CER"),
            Self::BadEoc => f.write_str("'Indefinite Length BER' includes a bad 'EOC.'"),
            Self::InvalidContents => f.write_str("Contents include invlid octet(s)."),
        }
    }
}

impl std::error::Error for Error {}
