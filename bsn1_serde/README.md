# bsn1_serde

`bsn1_serde` offers derive macros `Serialize` and `Deserialize`, similar to those found in the widely-known crate, `serde`. Designed to be used in conjunction with `bsn1`, it offers specialized serialization support tailored for the ASN.1 format.

While `serde` is renowned for its serialization/deserialization capabilities, it's fundamentally designed as a general-purpose framework. This means it might not handle all the special features of every format, like those in ASN.1.
ASN.1 has many unique features not commonly found in other serialization formats, making it hard to fit into the `serde` way of doing things.

`bsn1_serde` steps in to fill this gap by providing macros tailored for the ASN.1 format, taking inspiration from `serde`'s design.

See also [`bsn1`].

[`bsn1`]: https://crates.io/crates/bsn1

## Examples

'Lightweight Directory Access Protocol (LDAP)' adopts BER.
Let's make/parse LDAP Bind Request (i.e. Login Query.)

Note that BER consists of identifier and contents.
The identifier is composed of class, primitive/constructed flag, and number.

See [RFC4511](https://www.rfc-editor.org/rfc/rfc4511) for the details.

```
use bsn1::{ContentsRef, Error, Id, IdRef, Length};
use bsn1_serde::{de, from_ber, ser, to_ber, Deserialize, OctetString, Serialize};
use std::io::Write;

/// `BindRequest` represents the Bind Request (= login query) of LDAP.
/// We support only simple authentication (= password) here.
///
/// BindRequest ::= [APPLICATION 0] SEQUENCE {
///          version INTEGER (1 .. 127),
///          name LDAPDN,
///          authentication AuthenticationChoice }
///
/// LDAPDN ::= LDAPString
///            -- Constrained to <distinguishedName> [RFC4514]
///
/// LDAPString ::= OCTET STRING -- UTF-8 encoded,
///                             -- [ISO10646] characters
///
/// AuthenticationChoice ::= CHOICE {
///      simple                  [0] OCTET STRING,
///      -- 1 and 2 reserved
///      sasl                    [3] SaslCredentials,
///      ... }
///
/// Note that '[APPLICATION 0] SEQUENCE' stands for
/// "SEQUENCE, but the id class is 'APPLICATION', the id number is 0."
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[bsn1_serde(id = Sequence, tag_class = APPLICATION, tag_num = 0)]
struct BindRequest {
    version: i32,
    #[bsn1_serde(to = "OctetString::new", try_from = "OctetString")]
    name: String,
    authentication: SimpleAuth,
}

/// SimpleAuth represents the password.
///
/// Unfortunately, we cannot derive the implementation of the trait from `Serialize`
/// and `Deserialize` for this struct for now.
///
/// We implement them later.
///
/// AuthenticationChoice ::= CHOICE {
///      simple                  [0] OCTET STRING,
///      -- 1 and 2 reserved
///      sasl                    [3] SaslCredentials,
///      ... }
#[derive(Debug, PartialEq, Eq)]
struct SimpleAuth(Vec<u8>);

impl ser::Serialize for SimpleAuth {
    fn write_id<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        // '[0] OCTET STRING' means "Octet String, but the id number is 0."
        let mut id: Id = IdRef::octet_string().into();
        id.set_number(0_u8.into());

        buffer.write_all(id.as_ref() as &[u8]).map_err(Error::from)
    }

    fn write_der_contents<W: ?Sized + Write>(&self, buffer: &mut W) -> Result<(), Error> {
        buffer.write_all(&self.0[..]).map_err(Error::from)
    }

    fn id_len(&self) -> Result<usize, Error> {
        // The result is always `Ok(1)`.
        // You can write as `return Ok(1)`, of cause.
        let mut id: Id = IdRef::octet_string().into();
        id.set_number(0_u8.into());
        Ok(id.len())
    }

    fn der_contents_len(&self) -> Result<Option<usize>, Error> {
        Ok(Some(self.0.len()))
    }
}

impl de::Deserialize for SimpleAuth {
    unsafe fn from_ber(id: &IdRef, length: Length, contents: &ContentsRef) -> Result<Self, Error> {
        // Sanitize the id, however, the spec of RFC is ambiguous.
        //
        // '[0] OCTET STRING' does not refer to the class, but it is unnatural to change the number
        // of UNIVERSAL class. (OCTET STRING is UNIVERSAL.)
        //
        // BER allows both primitive and constructed OCTET STRING.
        //
        // Here, we check only the number.
        if id.number() != Ok(0_u8.into()) {
            return Err(Error::UnmatchedId);
        }

        // `SimpleAuth` should be deserialized as OCTET STRING except for the id.
        // We pass dummy id to delegate the task to `OctetString`.
        let slice: OctetString = OctetString::from_ber(IdRef::octet_string(), length, contents)?;
        Ok(Self(slice.into_vec()))
    }

    fn from_der(id: &IdRef, contents: &ContentsRef) -> Result<Self, Error> {
        // See the comment of [`from_ber`].
        if id.number() != Ok(0_u8.into()) {
            return Err(Error::UnmatchedId);
        }

        let slice: OctetString = OctetString::from_der(IdRef::octet_string(), contents)?;
        Ok(Self(slice.into_vec()))
    }
}

fn main() {
    // Build `BindRequest`.
    let version: i32 = 3; // The current LDAP version is '3'.
    let name: String = "uid=my_name,dc=my_company,dc=co,dc=jp".to_string();
    let password: Vec<u8> = Vec::from("open_sesami".as_bytes());

    let req = BindRequest {
        version,
        name,
        authentication: SimpleAuth(password),
    };

    // Serialize and deserialize `req`.
    // The result should be same to `req`.
    let serialized = to_ber(&req).unwrap();
    let deserialized: BindRequest = from_ber(&serialized).unwrap();

    assert!(req == deserialized);
}
```
