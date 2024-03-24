# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)

## 0.1.0 - 2024-02-01

### Added

- First release.

## 0.2.0 -

### Changed

- Wrap `TryFrom::Error` into `bsn1::Error::Anyhow`, instead of `bsn1::Error::Boxed`
- Enable attribute `#[bsn1\_serde(transparent)]` to treat struct with 2 or more than 2 fields as long as exactly 1 field is to be serialized/deserialized.
