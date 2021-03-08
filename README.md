# bsn1

`bsn1` treats 'ASN.1.'

## What is ASN.1?

ASN.1 stands for 'Abstruct Syntax Notation One' and X.690 is an 'ITU-T' standard specifying
the following ASN.1 encording formats.

- Basic Encoding Rules (BER)
- Canonical Encoding Rules (CER)
- Distinguished Encoding Rules (DER)

This crate supports BER and DER so far.

ASN.1 formats resembles 'JSON' in some ways, because they both are about serializing
structured data, however, they differs in the following points.

- JSON are easy for human to read, on the other hand, ASN.1 is readable for a computer.
  i.e. ASN.1 consumes less computer resources and less CPU time than JSON does.
- ASN.1 defines types 'Integer', 'Boolean', 'String', 'Sequence', and so on universally like
  JSON. What is more, ASN.1 allows for users to define a new data type.

ASN.1 has been used all over the world for a long time and very stable. For example,
'Transport Layer Security (TLS, SSL)', 'Lightweight Directory Access Protocol (LDAP)',
'4th Generation Mobile Communication System (4G)', and so on.

See ['X.690 (07/2002)'] for details.

['X.690 (07/2002)']: https://www.itu.int/ITU-T/studygroups/com17/languages/X.690-0207.pdf

## Feature of `bsn1`

`bsn1` treats user defined data as well as universal data types; while most other rust
crates can treat only universal data.

To be accurate, there are 4 classes in ASN.1; universal class, application class, context
specific class, and private class. `bsn1` knows all of them.

License: LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause
