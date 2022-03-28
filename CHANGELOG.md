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
