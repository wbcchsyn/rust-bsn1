# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)

## 0.1.0 - 2021-03-08

### Added

- First release.

## 0.2.0 - 2021-03-11

### Added

- Function 'Ber.into\_vec()'
- Function 'Der.into\_vec()'

## 0.3.0 - 2021-05-24

### Added

- Function 'Der::from\_id\_iterator()' and 'Ber::from\_id\_iterator()'.
- Functions to build universal class DERs and BERs.
  - 'Der::boolean()' and 'Ber::boolean()'.
  - 'Der::integer()' and 'Ber::integer()'.
  - 'Der::utf8\_string()' and 'Ber::utf8\_string()'.
  - 'Der::octet\_string()' and 'Ber::octet\_string()'.
- Implement trait 'TryFrom' for enum 'Length'.

### Changed

- Function 'length\_to\_bytes()' is renamed as 'Length::to\_bytes()'.

### Removed

- struct 'DerBuilder' and 'BerBuilder'. 'Der::from\_id\_iterator()' and 'Ber::from\_id\_iterator()' can usually be used instead.
- Function 'try\_length\_from()'. Use 'Length::try\_from()' instead.

## 0.3.1 - 2022-02-24

### Changed

- Update for rust the latest version.

## 0.4.0 - 2022-03-03

### Added

- Function 'contents::to\_integer\_unchecked()'

### Changed

- The following functions are made generic and take builtin primitive integer types as the argument.
  - 'contents::from\_integer()'
  - 'contents::to\_integer()'
- The following functions are made const.
  - 'contents::to\_bool\_ber()'
  - 'contents::to\_bool\_der()'

## 0.4.1 - 2022-03-28

### Added

- The following functions and methods.
  - Function 'Ber::from\_bytes()'
  - Function 'Ber::from\_bytes\_unchecked()'
  - Function 'Ber::from\_bytes\_starts\_with\_unchecked()'
  - Function 'BerRef::from\_bytes()'
  - Method 'BerRef::as\_bytes()'
  - Function 'DerRef::from\_bytes()'
  - Method 'DerRef::as\_bytes()'
  - Function 'Der::from\_bytes()'
  - Function 'Der::from\_bytes\_unchecked()'
  - Function 'Der::from\_bytes\_starts\_with\_unchecked()'
  - Function 'IdRef::from\_bytes()'
  - Method 'IdRef::as\_bytes()'
  - Function 'Id::from\_bytes()'
  - Function 'Ber::from\_bytes\_unchecked()'
- Implement 'PartialEq' for the following structs.
  - Ber
  - BerRef
  - Der
  - DerRef
  - IdRef
  - Id

## 0.9 - 2022-12-01

### Added

- Struct 'Contents' and 'ContentsRef'.
- The following trait implementations.
  - 'Hash' for struct 'Ber'
  - 'Hash' for struct 'BerRef'
  - 'Hash' for struct 'Der'
  - 'Hash' for struct 'DerRef'
  - DerefMut for 'Id'
- The following functions and methods.
  - IdRef::from\_bytes\_mut()
  - IdRef::from\_bytes\_mut\_unchecked()
  - IdRef.as\_bytes\_mut()
  - IdRef.set\_class()
  - IdRef.set\_pc()
  - Length::from\_bytes()
  - Length.len()
- Implementation of trait 'Send' and 'Sync' for the following structs.
  - Ber
  - Contents
  - Der
  - Id

### Changed

- The argument type of 'Ber::new()' and 'Der::new()'. (They take '&ContentsRef' instead of '&[u8]'.)
- The return type of 'BerRef.contents()' and 'DerRef.contents()'. (They return '&ContentsRef' instead of '&[u8]'.)
- The argument type of 'Id::new()'
- The argument type and the return type of 'IdRef.number()'. (It takes and returns builtin primitive integer types like u8, i128, and so on.)
- The return type of 'Length.to\_bytes()'. (It returns 'impl Deref<Target = [u8]>', instead of 'impl AsRef<[u8]>'.)

### Removed

- Module 'contents'; use functions of 'Contents' or 'ContentsRef' instead.
- BSD-2-Clause license
- The following trait implementations. ('Deref' and 'DerefMut' will do.)
  - AsRef\<BerRef\> for Ber
  - AsMut\<ContentsRef\> for Contents
  - AsRef\<ContentsRef\> for Contents
  - AsRef\<DerRef\> for Der
  - AsRef\<IdRef\> for Id
- The following build functions.
  - Ber::from\_bytes\_starts\_with\_unchecked()
  - BerRef::from\_bytes\_starts\_with\_unchecked()
  - Der::from\_bytes\_starts\_with\_unchecked()
  - DerRef::from\_bytes\_starts\_with\_unchecked()

### Fixed

- Enable to parse the identifier octets whose length is longer than or equals to 3 bytes.
- Make the check strict to parse integer contents.

## 1.0 - 2023-03-02

### Added

- The following trait implementations
  - DerefMut for Ber
  - TryFrom<&mut [u8]> for '&mut BerRef'
  - DerefMut for Der
  - TryFrom<&mut [u8]> for '&mut DerRef'
  - AsRef\<IdRef\> for Id
  - AsMut\<IdRef\> for Id
  - PartialOrd for Length
  - AsRef\<ContentsRef\> for Contents
  - AsMut\<ContentsRef\> for Contents
  - Index\<T\> for ContentsRef where T is bounded on SliceIndex<[u8]>
- The following functions and methods
  - Ber::new\_indefinite()
  - Ber::with\_id\_length()
  - Ber::with\_id\_length\_indefinite()
  - Ber.set\_length()
  - BerRef::try\_from\_mut\_bytes()
  - BerRef::from\_mut\_bytes\_unchecked()
  - BerRef.mut\_id()
  - BerRef.mut\_contents()
  - ContentsRef.\_as\_bytes()
  - ContentsRef.\_as\_mut\_bytes()
  - ContentsRef.is\_empty();
  - ContentsRef.len();
  - Der::with\_id\_length()
  - Der.set\_length()
  - DerRef::try\_from\_mut\_bytes()
  - DerRef::from\_mut\_bytes\_unchecked()
  - DerRef.mut\_id()
  - DerRef.mut\_contents()
  - Id.set\_number()
  - IdRef.len()
  - Length.definite()
  - Length.is\_definite()
  - Length.is\_indefinite()

### Changed

- Rename the following functions and methods
  - Ber::from\_bytes() -> Ber::try\_from\_bytes()
  - BerRef::from\_bytes() -> BerRef::try\_from\_bytes()
  - ContentsRef::from\_bytes\_mut() -> ContentsRef::from\_mut\_bytes()
  - Der::from\_bytes() -> Der::try\_from\_bytes()
  - DerRef::from\_bytes() -> DerRef::try\_from\_bytes()
  - Id::from\_bytes() -> Id::try\_from\_bytes()
  - IdRef::from\_bytes() -> IdRef::try\_from\_bytes()
  - IdRef::from\_bytes\_mut() -> IdRef::try\_from\_mut\_bytes()
  - IdRef::from\_bytes\_mut\_unchecked() -> IdRef::try\_from\_mut\_bytes\_unchecked()
  - IdRef.as\_bytes\_mut() -> IdRef.as\_mut\_bytes()
  - Length::from\_bytes() -> Length::try\_from\_bytes()
- Make the following functions and methods unsafe
  - IdRef.as\_mut\_bytes()
- `PartialEq::eq(Length::Indefinite, Length::Indefinite)` returns false, because they cannot be compared

### Removed

- Delete the implementations for the following traits
  - Borrow<[u8]> for Ber
  - Borrow<[u8]> for BerRef
  - Borrow<[u8]> for DerRef
  - Borrow<[u8]> for Contents
  - BorrowMut<[u8]> for Contents
  - Borrow<[u8]> for ContentsRef
  - BorrowMut<[u8]> for ContentsRef
  - Borrow<[u8]> for Id
  - Borrow<[u8]> for IdRef
  - Deref for IdRef
  - DerefMut for IdRef
  - Eq for Length
  - Ord for Contents
  - PartialOrd for Contents
  - PartialOrd for ContentsRef
  - Ord for ContentsRef

## 2.0 - 2023-03-02

### Added

- Implement the following traits
  - From\<bool\> for Ber
  - From\<T: PrimInt\> for Ber (`PrimInt` is `i8` or `u8` or ... `u128` or `isize` or `usize`.)
  - From\<&str\> for Ber
  - From\<&[u8]\> for Ber
  - From\<bool\> for Der
  - From\<T: PrimInt\> for Der (`PrimInt` is `i8` or `u8` or ... `u128` or `isize` or `usize`.)
  - From\<&str\> for Der
  - From\<&[u8]\> for Der
  - From\<&[u8; N]\> for Contents
  - From\<&[u8; N]\> for &ContentsRef
  - From\<&mut [u8; N]\> for &mut ContentsRef

### Changed

- Rename the following functions and methods
  - Rename Ber::try\_from\_bytes() Ber::parse()
  - Rename BerRef::try\_from\_bytes() Ber::parse()
  - Rename BerRef::try\_from\_mut\_bytes() Ber::parse\_mut()
  - Rename Der::try\_from\_bytes() Der::parse()
  - Rename DerRef::try\_from\_bytes() Der::parse()
  - Rename DerRef::try\_from\_mut\_bytes() Der::parse\_mut()
  - Rename Id::try\_from\_bytes() Id::parse()
  - Rename IdRef::try\_from\_bytes() IdRef::parse()
  - Rename IdRef::try\_from\_mut\_bytes() IdRef::parse\_mut()
  - Rename Length::try\_from\_bytes() Length::parse()

### Removed

- Delete the following builder functions. Use `From` implementation instead.
  - Ber::boolean()
  - Ber::integer()
  - Ber::octet_string()
  - Ber::utf8_string()
  - Der::boolean()
  - Der::integer()
  - Der::octet_string()
  - Der::utf8_string()
  - Contents::from\_bool()
  - ContentsRef::from\_bool()
  - ContentsRef::from\_bytes()
  - ContentsRef::from\_mut\_bytes()
- Ignore the following `TryFrom` implementations. Use `parse()` or `parse_mut()` instead.
  - TryFrom\<&[u8]\> for Ber
  - TryFrom\<&[u8]\> for &BerRef
  - TryFrom\<&mut [u8]\> for &mut BerRef
  - TryFrom\<&[u8]\> for Der
  - TryFrom\<&[u8]\> for &DerRef
  - TryFrom\<&mut [u8]\> for &mut DerRef
  - TryFrom\<&[u8]\> for Id
  - TryFrom\<&[u8]\> for IdRef
  - TryFrom\<&[u8]\> for Length
- Delete the following macros
  - constructed\_ber!()
  - constructed\_der!()
