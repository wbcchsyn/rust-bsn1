# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)

## 0.1.0 - 2024-02-01

### Added

- First release.

## 0.2.0 - 2024-04-03

### Changed

- Wrap `TryFrom::Error` into `bsn1::Error::Anyhow`, instead of `bsn1::Error::Boxed`
- Enable attribute `#[bsn1\_serde(transparent)]` to treat struct with 2 or more than 2 fields as long as exactly 1 field is to be serialized/deserialized.

### Fixed

- Make `BTreeMap` and `HashMap` error to deserialize from BER or DER if the key-value pair includes (an) extra octet(s).

### Changed

- Change the return type of `ser::Serialize.der\_contents\_len()`. It returns `Result<Option<usize>, Error>`, instead of `Result<usize, Error>`.
- Change the return type of `ser::Serialize.id\_len()`. It returns `Result<Option<usize>, Error>`, instead of `Result<usize, Error>`.
