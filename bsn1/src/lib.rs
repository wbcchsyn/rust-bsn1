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
    /// Wrapper of [`anyhow::Error`].
    ///
    /// Note that this error cannot be compared with others.
    /// `PartialEq::eq` always returns `false` for this error.
    Anyhow(anyhow::Error),
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
            Self::Anyhow(err) => err.fmt(f),
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
            Self::Anyhow(_) => false,
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Self::Io(err)
    }
}

impl From<anyhow::Error> for Error {
    fn from(err: anyhow::Error) -> Self {
        Self::Anyhow(err)
    }
}

impl Error {
    /// Consumes `self`, converting it into an [`anyhow::Error`].
    ///
    /// If `self` matches `Error::Anyhow`, returns the inner value;
    /// otherwise, wraps `self` and returns.
    pub fn into_anyhow(self) -> anyhow::Error {
        match self {
            Self::Anyhow(err) => err,
            _ => anyhow::Error::new(self),
        }
    }

    /// Returns a reference to the inner [`anyhow::Error`] if `self` is `Error::Anyhow`;
    /// otherwise, returns `None`.
    pub fn as_anyhow(&self) -> Option<&anyhow::Error> {
        match self {
            Self::Anyhow(err) => Some(err),
            _ => None,
        }
    }

    /// Consumes `self`, wrapping it with `context`.
    pub fn context<C>(self, context: C) -> Self
    where
        C: fmt::Display + Send + Sync + 'static,
    {
        self.into_anyhow().context(context).into()
    }

    /// If `self` matches `Error::Anyhow`, returns a reference to the first `Self` type error
    /// in the chain; otherwise, returns `self`.
    pub fn root_cause(&self) -> &Self {
        match self {
            Self::Anyhow(err) => {
                let mut ret = self;
                for cause in err.chain() {
                    if let Some(e) = cause.downcast_ref::<Self>() {
                        ret = e;
                    } else {
                        break;
                    }
                }
                return ret;
            }
            _ => self,
        }
    }
}
