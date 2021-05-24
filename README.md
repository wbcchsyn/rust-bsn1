# bsn1

`bsn1` is a rust library to serialize/deserialize in 'ASN.1' format.

Unlike to other crates, `bsn.1` is able to treat class 'Application', 'Context-specific',
and 'Private' as well as 'Universal'.

## What is ASN.1?

ASN.1 stands for 'Abstract Syntax Notation One' and X.690 is an 'ITU-T' standard specifying
the following ASN.1 encoding formats.

- Basic Encoding Rules (BER)
- Canonical Encoding Rules (CER)
- Distinguished Encoding Rules (DER)

This crate supports BER and DER for now.

ASN.1 resembles 'JSON' in some ways because they both are about serializing structured data,
however, they differ in the following points.

- JSON is easy for a human to read, on the other hand, ASN.1 is readable for a computer.
  i.e. ASN.1 consumes less computer resource like CPU time than JSON does.
- There are 4 classes in ASN.1 formats, 'Universal', 'Application', 'Context-specific',
  and 'Private'.
  Class 'Universal' defines types like 'Integer', 'Boolean', 'String', 'Sequence' and so on
  like JSON. What is more, ASN.1 allows users to define a new data type using other classes.

ASN.1 has been used all over the world for a long time and it is very stable. For example,
'Transport Layer Security (TLS, SSL)', 'Lightweight Directory Access Protocol (LDAP)',
'4th Generation Mobile Communication System (4G)', and so on.

See ['X.690 (07/2002)'] for details.

['X.690 (07/2002)']: https://www.itu.int/ITU-T/studygroups/com17/languages/X.690-0207.pdf

License: LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause
