# Glossary of terms

Attribute `bsn1_serde` annotates struct, enum, variant, and field.

```
struct S {      // <-- `S` is struct
    x: i32,     // <-- `x` is field
    y: String,  // <-- `y` is field, too
}

enum E {         // <-- `E` is enum
    A {          // <-- `A` is variant
        x: i32   // <-- `x` is field
    },
    B (          // <-- `B` is variant, too
        i32,     // <-- This i32 is field
        String,  // <-- This String is field, too
    )
}
```

# The structure of ASN.1 format

ASN.1 BER and DER consists of identifier and contents, and the identifier is composed of class, primitive/constructed flag (p/c flag), and number.

Remember that to read the following documents.

# \#\[bsn1\_serde(id = ..., tag\_class = ..., tag\_pc = ..., tag\_num = ...)\]

These arguments can be passed to attribute for struct or variant, and specifies the identifier.

## \#\[bsn1\_serde(id = type)\]

Specify the identifier.
`type` should be one of the followings.

- EOC (UNIVERSAL class, PRIMITIVE, number 0x00)
- Boolean (UNIVERSAL class, PRIMITIVE, number 0x01)
- Integer (UNIVERSAL class, PRIMITIVE, number 0x02)
- BitString (UNIVERSAL class, PRIMITIVE, number 0x03)
- OctetString (UNIVERSAL class, PRIMITIVE, number 0x04)
- Null (UNIVERSAL class, PRIMITIVE, number 0x05)
- Real (UNIVERSAL class, PRIMITIVE, number 0x09)
- UTF8String (UNIVERSAL class, PRIMITIVE, number 0x0c)
- Sequence (UNIVERSAL class, CONSTRUCTED, number 0x10)
- Set (UNIVERSAL class, CONSTRUCTED, number 0x11)

The default value is `Sequence`.

## \#\[bsn1\_serde(tag\_class = `UNIVERSAL` or `APPLICATION` or `CONTEXT_SPECIFIC` or `PRIVATE`)\]

Overwrite the class of the id specified via argument `id`.

## \#\[bsn1\_serde(tag\_pc = `PRIMITIVE` or `CONSTRUCTED`)\]

Overwrite the p/c flag of the id specified via argument `id`.

## \#\[bsn1\_serde(tag\_num = u128)\]

Overwrite the number of the id specified via argument `id`.

## Examples

```
use bsn1_serde::{to_der, Serialize, Deserialize};

/// A ::= SEQUENCE {
///         INTEEGER
///     }
#[derive(Serialize, Deserialize)]
struct A(i32);

/// B ::= SET {
///         INTEEGER,
///         UTF8 String,
///     }
#[derive(Serialize, Deserialize)]
#[bsn1_serde(id = Set)]
struct B {
    x: i32,
    y: String,
}

/// C ::= [APPLICATION 0] UTF8 String
#[derive(Serialize, Deserialize)]
#[bsn1_serde(id = UTF8String, tag_class = APPLICATION, tag_num = 0)]
struct C (String);

/// D ::= [APPLICATION PRIMITIVE 0x10] Integer
#[derive(Serialize, Deserialize)]
#[bsn1_serde(tag_class = APPLICATION, tag_pc = PRIMITIVE, tag_num = 0x10)]
struct D (i32);

/// X ::= CHOICE {
///         A SEQUENCE { INTEGER }
///         B SET { INTEGER, UTF8 String, }
///     }
#[derive(Serialize, Deserialize)]
enum X {
    A (i32),
    #[bsn1_serde(id = Set)]
    B {
        x: i32,
        y: String,
    },
}

// A and X::A is serialized in the same way.
let a = A (5);
let x = X::A(5);
assert!(to_der(&a).unwrap() == to_der(&x).unwrap());
```

## Warnings

The id of each variant should be different from each other in the same enum; otherwise, the implementation of `Deserialize` will not work well.

(It does not matter if you use only derive macro `Serialize`.)

# #\[bsn1\_serde(skip, skip_serializing, skip_deserializing, default = "...")\]

These arguments can be passed to attribute for field, and make quit to serialize/deserialize the annotated field.

## \#\[bsn1\_serde(skip)\]

Does not serialize/deserialize the annotated field.
(Same to pass both `skip_serializing` and `skip_deserializing`.)

When deserializing, this crate use `Default::default` or function given by `default = "..."` to get the value of the field.

## \#\[bsn1\_serde(skip\_serializing)\]

Does not serialize the annotated field.

## \#\[bsn1\_serde(skip\_deserializing)\]

Does not deserialize the annotated field.

When deserializing, this crate use `Default::default` or function given by `default = "..."` to get the value of the field.

## \#\[bsn1\_serde(default = "Path\_to\_builder\_function")\]

This crate use the specified function to get the value of the field to deserialize if `skip` or `skip_deserializing` is passed as well.

The builder function must be callable as `fn() -> T` where `T` is the type of the field.

## Examples

```
use bsn1_serde::{from_der, to_der, Serialize, Deserialize};

/// A ::= SEQUENCE {
///         INTEEGER,
///         UTF8 String,
///     }
#[derive(Serialize, Deserialize)]
struct A {
    x: i32,
    y: String,
    #[bsn1_serde(skip)]
    z: i32,
    #[bsn1_serde(skip_serializing, skip_deserializing, default = "A::one")]
    w: i32
}

impl A {
    fn one() -> i32 {
        1
    }
}

// Build a new instance of `A`.
let a = A {
    x: 1,
    y: "foo".to_string(),
    z: 2,
    w: 3,
};

// Serialize and deserialize `a`.
let serialized = to_der(&a).unwrap();
let deserialized: A = from_der(&serialized).unwrap();

// The default value is set to the skipped fields.
assert!(deserialized.x == a.x);
assert!(deserialized.y == a.y);
assert!(deserialized.z == Default::default());
assert!(deserialized.w == A::one());
```

# \#\[bsn1\_serde(from = "...", try\_from = "...", into = "...", to = "...")\]

These arguments can be passed to attribute for struct or enum or field, and converts them to serialize/deserialize.

## \#\[bsn1\_serde(from = "FromType")\]

Deserializes into `FromType`, and then converting. `FromType` must implements `de::Deserialize` and the annotated struct or enum or field must implements `From<FromType>`.

Fields with `from` are not required to implement `de::Deserialize`.

## \#\[bsn1\_serde(try\_from = "TryFromType")\]

Deserializes into `TryFromType`, and then converting. `TryFromType` must implements `de::Deserialize` and the annotated struct or enum or field must implements `TryFrom<TryFromType>`.

If `TryFrom::try_from` fails, wraps the error into [`::bsn1::Error`] and returns it.

Fields with `try_from` are not required to implement `de::Deserialize`.

## \#\[bsn1\_serde(into = "IntoType")\]

Clones and converts into `IntoType`, and then serializing. `IntoType` must implements `ser::Serialize` and the annotated struct or enum or field must implements `Clone` and `Into<IntoType>`.

This argument is analogous to that of `serde` crate.
It would be better to use argument `to` instead, because `to` does not clones it.

Fields with `into` are not required to implement `ser::Serialize`.

## \#\[bsn1\_serde(to = "Path\_to\_converting\_function")\]

Converts the annotated struct or enum or field using the specified function, and then serializing.

The converting function must be callable as `fn(&T) -> U` where `T` is the type of the annotated struct or enum or field, and `U` must implements `ser::Serialize`.

Fields with `to` are not required to implement `ser::Serialize`.

## Examples

```
use bsn1_serde::{from_der, to_der, Deserialize, OctetString, Serialize};

/// A ::= INTEGER
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[bsn1_serde(into = "u16", from = "u16")]
struct A {
    x: u8,
    y: u8,
}

impl From<u16> for A {
    fn from(val: u16) -> Self {
        let x = (val / 256) as u8;
        let y = (val % 256) as u8;
        Self { x, y }
    }
}

impl Into<u16> for A {
    fn into(self) -> u16 {
        let x = self.x as u16;
        let y = self.y as u16;
        x * 256 + y
    }
}

// Build a new instance of `A`.
let a = A {
    x: 1,
    y: 2,
};

// Serialize and deserialize `a`.
let serialized = to_der(&a).unwrap();
let deserialized: A = from_der(&serialized).unwrap();
assert!(a == deserialized);

// `serialized` can be deserialized as `u16` as well,
// because `a` is converted as `u16` when serialized.
let deserialized: u16 = from_der(&serialized).unwrap();
assert!(deserialized == (a.x as u16) * 256 + (a.y as u16));

/// B ::= [PRIVATE] SEQUENCE {
///         OCTET STRING
///     }
#[derive(Serialize, Deserialize)]
#[bsn1_serde(tag_class = PRIVATE)]
struct B(#[bsn1_serde(to = "OctetString::new", try_from = "OctetString")] String);
```

# \#\[bsn1\_serde(transparent)\]

`transparent` can be passed to attribute for struct with one field.

Serializes and deserializes the annotated struct exactly the same as if the field were serialized and deserialized by itself.

## Examples

```
use bsn1_serde::{from_der, to_der, Deserialize, OctetString, Serialize};

/// A ::= UTF8 String
#[derive(PartialEq, Eq, Serialize, Deserialize)]
#[bsn1_serde(transparent)]
struct A (String);

// Build a new instance of `A`.
let a = A("foo".to_string());

// Serialize and deserialize.
let serialized = to_der(&a).unwrap();
let deserialized: A = from_der(&serialized).unwrap();
assert!(a == deserialized);

// `serialized` can be deserialized as `String` as well,
// because `a` is serialized exactly the same way as if the field were serialized.
let deserialized: String = from_der(&serialized).unwrap();
assert!(a.0 == deserialized);

/// B ::= OctetString
#[derive(PartialEq, Eq, Serialize, Deserialize)]
#[bsn1_serde(transparent)]
struct B {
    #[bsn1_serde(to = "OctetString::new", try_from = "OctetString")]
    x: String,
}

// Build a new instance of `B`.
let b = B { x: "bar".to_string() };

// Serialize and deserialize.
let serialized = to_der(&b).unwrap();
let deserialized: B = from_der(&serialized).unwrap();
assert!(b == deserialized);

// `serialized` can be deserialized as `OctetString` as well.
let deserialized: OctetString = from_der(&serialized).unwrap();
assert!(OctetString::new(&b.x) == deserialized);
```
