# bsn1

`bsn1` is a rust library to serialize/deserialize in 'ASN.1' format.

## What is ASN.1?

ASN.1 stands for 'Abstract Syntax Notation One' and X.690 is an 'ITU-T' standard specifying
the following ASN.1 encoding format.

- Basic Encoding Rules (BER)
- Canonical Encoding Rules (CER)
- Distinguished Encoding Rules (DER)

This crate supports BER and DER for now.

ASN.1 resembles 'JSON' in some ways because they both are standard serializing structured data,
however, they differ in the following points.

- JSON is easy for a person to read, on the other hand, ASN.1 is readable for a computer.
  i.e. ASN.1 consumes less computer resources (e.g. CPU time) than JSON does.
- There are 4 classes in ASN.1 formats, 'Universal', 'Application', 'Context-specific',
  and 'Private'.
  Class 'Universal' defines types like 'Integer', 'Boolean', 'String', 'Sequence' and so on
  like JSON. What is more, ASN.1 allows users to define a new data type using another class.

ASN.1 has been used all over the world for a long time and it is very stable. For example,
'Transport Layer Security (TLS, SSL)', 'Lightweight Directory Access Protocol (LDAP)',
'4th Generation Mobile Communication System (4G)', and so on.

See also [X.690 (07/2002)] and [Wikipedia].

[X.690 (07/2002)]: https://www.itu.int/ITU-T/studygroups/com17/languages/X.690-0207.pdf
[Wikipedia]: https://en.wikipedia.org/wiki/X.690

## bsn1_serde

[`bsn1_serde`] offers derive macros `Serialize` and `Deserialize`, similar to those found in the widely-known crate, `serde`. Designed to be used in conjunction with `bsn1`, it offers specialized serialization support tailored for the ASN.1 format.

While `serde` is renowned for its serialization/deserialization capabilities, it's fundamentally designed as a general-purpose framework. This means it might not handle all the special features of every format, like those in ASN.1.
ASN.1 has many unique features not commonly found in other serialization formats, making it hard to fit into the `serde` way of doing things.

[`bsn1_serde`] steps in to fill this gap by providing macros tailored for the ASN.1 format, taking inspiration from `serde`'s design.

See also [`bsn1_serde`].

## Examples

'Lightweight Directory Access Protocol (LDAP)' adopts BER.
Let's make/parse LDAP Bind Operation (i.e. Login Query.)

See [RFC4511](https://www.rfc-editor.org/rfc/rfc4511) for the details.

```
use bsn1::{Ber, BerRef, ContentsRef, Id, IdRef, ClassTag, PCTag};

/// Creates a BindRequest from `name` and `password`.
///
/// BindRequest ::= [APPLICATION 0] SEQUENCE {
///          version INTEGER (1 .. 127),
///          name LDAPDN,
///          authentication AuthenticationChoice }
fn new_bind_request(name: &str, password: &[u8]) -> Ber {
    // BindRequest is constituted of version, name, and authentication.
    // '[APPLICATION 0] SEQUENCE' means "a sequence, but the class is APPLICATION, and the
    // number is 0."
    // The RFC does not refer to the Primitive/Constructed flag,
    // but SEQUENCE is usually Constructed.
    const ID_NUMBER: u32 = 0;
    let id = Id::new(ClassTag::Application, PCTag::Constructed, ID_NUMBER.into());

    let contents = [new_bind_version(), new_bind_name(name),
                    new_bind_authentication(password)];

    Ber::from_id_iterator(&id, contents.iter())
}

/// Creates a `version` for bind request.
/// This function always returns 3 (the current latest version.)
fn new_bind_version() -> Ber {
    Ber::from(3_i32)
}

/// Creates a `name` for bind request from `name`.
///
/// LDAPDN ::= LDAPString
///            -- Constrained to <distinguishedName> [RFC4514]
///
/// LDAPString ::= OCTET STRING -- UTF-8 encoded,
///                             -- [ISO10646] characters
fn new_bind_name(name: &str) -> Ber {
    Ber::from(name.as_bytes())
}

/// Creates a `simple authentication` for bind request from `password`.
///
/// AuthenticationChoice ::= CHOICE {
///      simple                  [0] OCTET STRING,
///      -- 1 and 2 reserved
///      sasl                    [3] SaslCredentials,
///      ... }
fn new_bind_authentication(password: &[u8]) -> Ber {
   // 'AuthenticationChoice' is either 'simple [0] OCTET STRING' or 'sasl [3] SaslCredentials'.
   // This function selects 'simple'.
   //
   // '[0] OCTET STRING' means "OCTET STRING, but the number is 0."
   // RFC does not refer to the class and Primitive/Constructed flag.
   // This function returns ContextSpecific and Primitive BER.
   const ID_NUMBER: u32 = 0;
   let id = Id::new(ClassTag::ContextSpecific, PCTag::Primitive, ID_NUMBER.into());

   let contents: &ContentsRef = password.into();

   Ber::new(&id, contents)
}

/// Tries to parse bind request and returns `(name, password)`.
fn parse_bind_request(req: &[u8]) -> Result<(&str, &[u8]), String> {
    // `req` should be a 'BER' and must not include any extra octets.
    let mut bytes = req;
    let req = BerRef::parse(&mut bytes)
                .map_err(|e| format!("Failed to parse the request as a BER: {}", e))?;
    if bytes.is_empty() == false {
        return Err("There are some bad octets at the end of the request.".to_string());
    }

    // Check the identifier of the request.
    let id = req.id();
    if id.class() != ClassTag::Application || id.number() != Ok(0_u8.into()) {
        return Err("The id of the request is bad.".to_string());
    }

    // Parse the contents of the request.
    // The contents should be composed of version, name, and authentication in this order.
    let mut bytes: &[u8] = req.contents().as_ref();

    let version = parse_bind_version(&mut bytes)?;
    if version != 3 {
        return Err("This function supports only version 3.".to_string());
    }

    let name = parse_bind_name(&mut bytes)?;
    let password = parse_bind_authentication(&mut bytes)?;

    Ok((name, password))
}

/// Tries to parse the version of bind request.
fn parse_bind_version(bytes: &mut &[u8]) -> Result<i32, String> {
    let ber = BerRef::parse(bytes).map_err(|e| format!("Failed to parse the version: {}", e))?;

    if ber.id() != IdRef::integer() {
        Err("The id of the version is bad.".to_string())
    } else {
        ber.contents()
           .to_integer()
           .map_err(|e| format!("Failed to parse the version: {}", e))
    }
}

/// Tries to parse the name of bind request.
fn parse_bind_name<'a>(bytes: &mut &'a [u8]) -> Result<&'a str, String> {
    let ber = BerRef::parse(bytes).map_err(|e| format!("Failed to parse the name: {}", e))?;

    if ber.id() != IdRef::octet_string() && ber.id() != IdRef::octet_string_constructed() {
        Err("The id of the name is bad.".to_string())
    } else {
        let contents = ber.contents().as_ref();
        std::str::from_utf8(contents).map_err(|e| format!("Failed to parse the name: {}", e))
    }
}

/// Tries to parse the password of bind request.
fn parse_bind_authentication<'a>(bytes: &mut &'a [u8]) -> Result<&'a [u8], String> {
    let ber = BerRef::parse(bytes)
                     .map_err(|e| format!("Failed to parse the authentication: {}", e))?;

    if ber.id().number() == Ok(3_u8.into()) {
        Err("This function supports only simple authentication".to_string())
    } else if ber.id().number() == Ok(0_u8.into()) {
        Ok(ber.contents().as_ref())
    } else {
        Err("The id of the authentication is bad".to_string())
    }
}

// Create a bind request
let name = "uid=user,dc=my_company,dc=co,dc=jp";
let password = "open_sesami".as_bytes();
let request = new_bind_request(name, password);

// The client will send the byte to the server actually.
let bytes = request.as_ref();

// The LDAP server will parse the request.
let (name_, password_) = parse_bind_request(bytes).unwrap();

assert_eq!(name, name_);
assert_eq!(password, password_);
```

[`bsn1_serde`]: https://crates.io/crates/bsn1_serde
