# bsn1_serde

`bsn1_serde` offers derive macros `Serialize` and `Deserialize`, similar to those found in the widely-known crate, `serde`. Designed to be used in conjunction with `bsn1`, it offers specialized serialization support tailored for the ASN.1 format.

While `serde` is renowned for its serialization/deserialization capabilities, it's fundamentally designed as a general-purpose framework. This means it might not handle all the special features of every format, like those in ASN.1.
ASN.1 has many unique features not commonly found in other serialization formats, making it hard to fit into the `serde` way of doing things.

`bsn1_serde` steps in to fill this gap by providing macros tailored for the ASN.1 format, taking inspiration from `serde`'s design.

See also [`bsn1`].

[`bsn1`]: https://crates.io/crates/bsn1
