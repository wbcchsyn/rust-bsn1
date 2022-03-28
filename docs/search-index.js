var searchIndex = JSON.parse('{\
"bsn1":{"doc":"<code>bsn1</code> is a rust library to serialize/deserialize in ‘ASN.1…","t":[13,13,3,3,4,13,13,13,3,3,4,3,3,13,13,13,4,13,4,13,13,13,13,13,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,14,14,0,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,12,5,5,5,5,5,5],"n":["Application","BadEoc","Ber","BerRef","ClassTag","Constructed","ContextSpecific","Definite","Der","DerRef","Error","Id","IdRef","Indefinite","IndefiniteLength","InvalidContents","Length","OverFlow","PCTag","Primitive","Private","RedundantBytes","UnTerminatedBytes","Universal","as_bytes","as_bytes","as_bytes","as_ref","as_ref","as_ref","as_ref","as_ref","as_ref","as_ref","as_ref","as_ref","bit_string","bit_string_constructed","bmp_string","bmp_string_constructed","boolean","boolean","boolean","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","character_string","character_string_constructed","class","clone","clone","clone","clone","clone","clone","clone","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","cmp","cmp","cmp","cmp","constructed_ber","constructed_der","contents","contents","contents","deref","deref","deref","embedded_pdv","enumerated","eoc","eq","eq","eq","eq","eq","eq","eq","eq","eq","eq","eq","eq","eq","eq","eq","eq","external","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","from","from","from","from","from","from","from","from","from","from","from","from_bytes","from_bytes","from_bytes","from_bytes","from_bytes","from_bytes","from_bytes_starts_with_unchecked","from_bytes_starts_with_unchecked","from_bytes_starts_with_unchecked","from_bytes_starts_with_unchecked","from_bytes_unchecked","from_bytes_unchecked","from_bytes_unchecked","from_bytes_unchecked","from_bytes_unchecked","from_bytes_unchecked","from_id_iterator","from_id_iterator","general_string","general_string_constructed","generalized_time","generalized_time_constructed","graphic_string","graphic_string_constructed","hash","hash","hash","hash","hash","hash","ia5_string","ia5_string_constructed","id","id","integer","integer","integer","into","into","into","into","into","into","into","into_vec","into_vec","is_application","is_constructed","is_context_specific","is_primitive","is_private","is_universal","length","length","ne","ne","ne","ne","ne","ne","ne","new","new","new","null","number","numeric_string","numeric_string_constructed","object_descriptor","object_identifier","octet_string","octet_string","octet_string","octet_string_constructed","partial_cmp","partial_cmp","partial_cmp","partial_cmp","pc","printable_string","printable_string_constructed","real","relative_oid","sequence","set","t61_string","t61_string_constructed","to_bytes","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_string","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","universal_string","universal_string_constructed","utc_time","utc_time_constructed","utf8_string","utf8_string","utf8_string","utf8_string_constructed","videotex_string","videotex_string_constructed","visible_string","visible_string_constructed","0","from_bool","from_integer","to_bool_ber","to_bool_der","to_integer","to_integer_unchecked"],"q":["bsn1","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","bsn1::Length","bsn1::contents","","","","",""],"d":["Application Tag","The contents of ‘EOC’ of the ‘Indefinite Length BER…","<code>Ber</code> owns <code>BerRef</code> and represents a BER.","<code>BerRef</code> is a wrapper of <code>[u8]</code> and represents a BER.","<code>ClassTag</code> represents Tag class of identifier.","Constructed data type.","Context-Specific Tag","‘Definite’ is for ‘BER’, ‘DER’, and ‘CER’, …","<code>Der</code> owns <code>DerRef</code> and represents DER.","<code>DerRef</code> is a wrapper of <code>[u8]</code> and represents DER.","Errors for this crate.","<code>Id</code> owns <code>IdRef</code> and represents Identifier.","<code>IdRef</code> is a wrapper of <code>[u8]</code> represents Identifier.","Represents ‘Indefinite’ length.","‘Indefinite length’ used in DER or CER. (It is only …","The contents includes some invalid octet(s).","<code>Length</code> represents ASN.1 length.","Over flow is occurred to parse bytes as a number.","<code>PCTag</code> represents Primitive/Constructed flag of identifier.","Primitive data type.","Private Tag","The bytes includes some redundant octet(s). (‘ASN.1’ …","The bytes finishes before the last octet.","Universal Tag","Provides a reference to the inner slice.","Provides a reference to the inner slice.","Provides a reference to the inner slice.","","","","","","","","","","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Returns a new instance representing boolean.","Returns a new instance representing boolean.","Provides a reference to <code>IdRef</code> representing ‘Universal …","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Returns <code>ClassTag</code> of <code>self</code> .","","","","","","","","","","","","","","","","","","","Builds a <code>Ber</code> instance representing Constructed BER …","Builds a <code>Der</code> instance representing ‘Constructed DER’ …","Provides functions to serialize/deserialize contents …","Provides a reference to the ‘contents’ octets of <code>self</code> .","Returns a reference to the contents octets of <code>self</code> .","","","","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","","","","","","","","","","","","","","","","","Provides a reference to <code>IdRef</code> representing ‘Universal …","","","","","","","","","","","","","","","","","","","","","","","Parses <code>bytes</code> starting with octets of ‘ASN.1 BER’ and …","Parses <code>bytes</code> starting with BER octets and builds a new …","Parses <code>bytes</code> starting with octets of ‘ASN.1 DER’ and …","Parses <code>bytes</code> starting with DER octets and builds a new …","Parses <code>bytes</code> starts with identifier and tries to build a …","Parses <code>bytes</code> starts with identifier and tries to build a …","Provides a reference from <code>bytes</code> that starts with a BER …","Builds a new instance from <code>bytes</code> that starts with ‘BER’…","Provides a reference from <code>bytes</code> that starts with a DER.","Builds a new instance from <code>bytes</code> that starts with ‘DER’…","Provides a reference from <code>bytes</code> without any sanitization.","Builds a new instance holding <code>bytes</code> without any …","Provides a reference from <code>bytes</code> without any sanitization.","Builds a new instance holding <code>bytes</code> without any …","Provides a reference from <code>bytes</code> without any sanitize. <code>bytes</code>…","Provides a reference from <code>bytes</code> without any sanitize. <code>bytes</code>…","Creates a new instance from <code>id</code> and <code>contents</code> .","Creates a new instance from <code>id</code> and <code>contents</code> .","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","","","","","","","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> of <code>self</code> .","Returns a reference to <code>IdRef</code> of <code>self</code> .","Returns a new instance representing integer.","Returns a new instance representing integer.","Provides a reference to <code>IdRef</code> representing ‘Universal …","","","","","","","","Consumes <code>self</code> , returning <code>Vec</code> .","Consumes <code>self</code> , returning <code>Vec</code> .","Returns <code>true</code> if <code>self</code> is ‘Application’ class, or <code>false</code> .","Returns <code>true</code> if <code>self</code> is flagged as ‘Constructed’, or …","Returns <code>true</code> if <code>self</code> is ‘Context Specific’ class, or …","Returns <code>true</code> if <code>self</code> is flagged as ‘Primitive’, or …","Returns <code>true</code> if <code>self</code> is ‘Private’ class, or <code>false</code> .","Returns <code>true</code> if <code>self</code> is ‘Universal’ class, or <code>false</code> .","Returns <code>Length</code> of <code>self</code> .","Returns <code>Length</code> to represent the length of contents.","","","","","","","","Creates a new instance from <code>id</code> and <code>contents</code> with definite …","Creates a new instance from <code>id</code> and <code>contents</code> .","Creates a new instance from <code>class</code> , <code>pc</code> , and <code>number</code> .","Provides a reference to <code>IdRef</code> representing ‘Universal …","Returns the number of <code>self</code> unless overflow.","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Returns a new instance representing octet_string.","Returns a new instance representing octet_string.","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","","","","","Returns the Primitive/Constructed flag of <code>self</code> .","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal Set…","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Serializes <code>length</code> .","","","","","","","","","","","","","Parses <code>bytes</code> starting with octets of ‘ASN.1 BER’ and …","","Parses <code>bytes</code> starting with DER octets and builds a new …","","","","Parses <code>bytes</code> starts with identifier octets and tries to …","Parses <code>bytes</code> starting with length octets and returns a …","","","","","","","","","","","","","","","","","","","","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Returns a new instance representing utf8_string.","Returns a new instance representing utf8_string.","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","Provides a reference to <code>IdRef</code> representing ‘Universal …","","Serializes boolean as contents octets.","Serializes integer as contents octets.","Parses <code>bytes</code> as a BER contents of Bool.","Parses <code>bytes</code> as a DER contents of Bool.","Parses <code>bytes</code> as a contents of Integer.","Parses <code>bytes</code> as a contents of Integer without any …"],"i":[1,2,0,0,0,3,1,4,0,0,0,0,0,4,2,2,0,2,0,3,1,2,2,1,5,6,7,5,8,8,6,9,9,7,10,10,7,7,7,7,8,9,7,5,5,8,8,8,6,6,9,9,9,1,3,7,7,10,10,10,4,2,5,8,6,9,1,3,7,10,4,2,7,7,7,8,9,1,3,10,4,2,8,9,1,3,10,4,2,1,3,7,10,0,0,0,5,6,8,9,10,7,7,7,5,5,8,8,6,6,9,9,1,3,7,7,10,10,4,2,7,5,8,6,9,1,3,7,10,4,2,2,8,8,8,8,9,9,1,3,10,4,2,5,8,6,9,7,10,5,8,6,9,5,8,6,9,7,10,8,9,7,7,7,7,7,7,1,3,7,10,4,2,7,7,5,6,8,9,7,8,9,1,3,10,4,2,8,9,7,7,7,7,7,7,5,6,5,8,6,9,7,10,4,8,9,10,7,7,7,7,7,7,8,9,7,7,1,3,7,10,7,7,7,7,7,7,7,7,7,4,5,8,6,9,1,3,7,10,4,2,2,8,8,9,9,1,3,10,10,4,4,2,8,9,1,3,10,4,2,5,8,6,9,1,3,7,10,4,2,7,7,7,7,8,9,7,7,7,7,7,7,11,0,0,0,0,0,0],"f":[null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,[[]],[[]],[[]],[[]],[[],["berref",3]],[[]],[[]],[[]],[[],["derref",3]],[[]],[[],["idref",3]],[[]],[[]],[[]],[[]],[[]],[[["bool",15]]],[[["bool",15]]],[[]],[[]],[[]],[[]],[[]],[[],["berref",3]],[[]],[[]],[[]],[[]],[[],["derref",3]],[[]],[[]],[[]],[[]],[[]],[[],["idref",3]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["classtag",4]],[[],["ber",3]],[[],["der",3]],[[],["classtag",4]],[[],["pctag",4]],[[],["id",3]],[[],["length",4]],[[],["error",4]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[["classtag",4]],["ordering",4]],[[["pctag",4]],["ordering",4]],[[["idref",3]],["ordering",4]],[[["id",3]],["ordering",4]],null,null,null,[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[["berref",3]],["bool",15]],[[["ber",3]],["bool",15]],[[["ber",3]],["bool",15]],[[["berref",3]],["bool",15]],[[["derref",3]],["bool",15]],[[["der",3]],["bool",15]],[[["der",3]],["bool",15]],[[["derref",3]],["bool",15]],[[["classtag",4]],["bool",15]],[[["pctag",4]],["bool",15]],[[["id",3]],["bool",15]],[[["idref",3]],["bool",15]],[[["idref",3]],["bool",15]],[[["id",3]],["bool",15]],[[["length",4]],["bool",15]],[[["error",4]],["bool",15]],[[]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[["der",3]]],[[["berref",3]]],[[]],[[["derref",3]]],[[["derref",3]]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["result",4,[["error",4]]]],[[],["result",4,[["error",4]]]],[[],["result",4,[["error",4]]]],[[],["result",4,[["error",4]]]],[[],["result",4,[["error",4]]]],[[],["result",4,[["error",4]]]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[["idref",3]]],[[["idref",3]]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["idref",3]],[[],["idref",3]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["vec",3,[["u8",15]]]],[[],["vec",3,[["u8",15]]]],[[],["bool",15]],[[],["bool",15]],[[],["bool",15]],[[],["bool",15]],[[],["bool",15]],[[],["bool",15]],[[],["length",4]],[[],["length",4]],[[["berref",3]],["bool",15]],[[["ber",3]],["bool",15]],[[["derref",3]],["bool",15]],[[["der",3]],["bool",15]],[[["idref",3]],["bool",15]],[[["id",3]],["bool",15]],[[["length",4]],["bool",15]],[[["idref",3]]],[[["idref",3]]],[[["classtag",4],["pctag",4],["u128",15]]],[[]],[[],["result",4,[["u128",15],["error",4]]]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[["classtag",4]],["option",4,[["ordering",4]]]],[[["pctag",4]],["option",4,[["ordering",4]]]],[[["idref",3]],["option",4,[["ordering",4]]]],[[["id",3]],["option",4,[["ordering",4]]]],[[],["pctag",4]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["string",3]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[]],[[]],[[]],[[]],[[["str",15]]],[[["str",15]]],[[]],[[]],[[]],[[]],[[]],[[]],null,[[["bool",15]]],[[]],[[],["result",4,[["bool",15],["error",4]]]],[[],["result",4,[["bool",15],["error",4]]]],[[],["result",4,[["error",4]]]],[[]]],"p":[[4,"ClassTag"],[4,"Error"],[4,"PCTag"],[4,"Length"],[3,"BerRef"],[3,"DerRef"],[3,"IdRef"],[3,"Ber"],[3,"Der"],[3,"Id"],[13,"Definite"]]}\
}');
if (window.initSearch) {window.initSearch(searchIndex)};