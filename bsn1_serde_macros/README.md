# bsn1_serde_macros

`bsn1_serde_macros` implements derive macros `Serialize` and `Deserialize` for crate `bsn1_serde`.

This crate is extracted from `bsn1_serde` because it is impossible for Rust crate implementing proc macro to publish any other things, like functions, structs, traits, and so on.
Because Rust crate implementing proc macro cannot publish any other thing, so this crate
