# Change Log
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)

## 0.1.0 - 2021-03-08
### Added
- First release.

## 0.2.0 - 2021-03-11
## Added
- Function 'Ber.into\_vec()'
- Function 'Der.into\_vec()'

## 0.3.0 - 2021-05-24
## Added
- Function 'Der::from\_id\_iterator()' and 'Ber::from\_id\_iterator()'.
- Functions to build universal class DERs and BERs.
    - 'Der::boolean()' and 'Ber::boolean()'.
    - 'Der::integer()' and 'Ber::integer()'.
    - 'Der::utf8\_string()' and 'Ber::utf8\_string()'.
    - 'Der::octet\_string()' and 'Ber::octet\_string()'.
- Implement trait 'TryFrom' for enum 'Length'.

## Changed
- Function 'length\_to\_bytes()' is renamed as 'Length::to\_bytes()'.

## Removed
- struct 'DerBuilder' and 'BerBuilder'. 'Der::from\_id\_iterator()' and 'Ber::from\_id\_iterator()' can usually be used instead.
- Function 'try\_length\_from()'. Use 'Length::try\_from()' instead.
