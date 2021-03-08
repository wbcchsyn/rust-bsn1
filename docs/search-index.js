var searchIndex = JSON.parse('{\
"bsn1":{"doc":"`bsn1` treats \'ASN.1.\'","i":[[3,"Ber","bsn1","`Ber` owns `BerRef` and represents a BER.",null,null],[3,"BerBuilder","","`BerBuilder` is a struct to build `Ber` effectively.",null,null],[3,"BerRef","","`BerRef` is a wrapper of `[u8]` and represents a BER.",null,null],[3,"Der","","`Der` owns `DerRef` and represents DER.",null,null],[3,"DerBuilder","","`DerBuilder` is a struct to build `Der` effectively.",null,null],[3,"DerRef","","`DerRef` is a wrapper of `[u8]` and represents DER.",null,null],[3,"Id","","`Id` owns `IdRef` and represents Identifier.",null,null],[3,"IdRef","","`IdRef` is a wrapper of `[u8]` represents Identifier.",null,null],[4,"ClassTag","","`ClassTag` represents Tag class of identifier.",null,null],[13,"Universal","","Universal Tag",0,null],[13,"Application","","Application Tag",0,null],[13,"ContextSpecific","","Context-Specific Tag",0,null],[13,"Private","","Private Tag",0,null],[4,"PCTag","","`PCTag` represents Private/Constructed flag of identifier.",null,null],[13,"Primitive","","Primitive data type.",1,null],[13,"Constructed","","Constructed data type.",1,null],[4,"Length","","`Length` represents ASN.1 length.",null,null],[13,"Indefinite","","Represents \'Indefinite\' length.",2,null],[13,"Definite","","\'Definite\' is for \'BER\', \'DER\', and \'CER\', and represents…",2,null],[4,"Error","","Errors for this crate.",null,null],[13,"UnTerminatedBytes","","The bytes finishes before the last octet.",3,null],[13,"RedundantBytes","","The bytes includes some redundant octet(s). (\'ASN.1\' does…",3,null],[13,"OverFlow","","Over flow is occurred to parse bytes as a number.",3,null],[13,"IndefiniteLength","","\'Indefinite length\' used in DER or CER. (It is only for…",3,null],[13,"BadEoc","","The contents of \'EOC\' of the \'Indefinite Length BER\' must…",3,null],[13,"InvalidContents","","The contents includes some invalid octet(s).",3,null],[5,"length_to_bytes","","Serializes `length` .",null,[[["length",4]]]],[5,"try_length_from","","Tries to parse `bytes` starting with \'length\' and returns…",null,[[],[["result",4],["error",4]]]],[11,"from_bytes_unchecked","","Provides a reference from `bytes` without any sanitization.",4,[[]]],[11,"from_bytes_starts_with_unchecked","","Provides a reference from `bytes` that starts with a BER…",4,[[]]],[11,"id","","Provides a reference to the `IdRef` of `self` .",4,[[],["idref",3]]],[11,"length","","Returns `Length` of `self` .",4,[[],["length",4]]],[11,"contents","","Provides a reference to the \'contents\' of `self` .",4,[[]]],[11,"new","","Creates a new instance from `id` and `contents` with…",5,[[["idref",3]]]],[11,"new","","Creates a new instance to build `Der` with `id` and…",6,[[["idref",3],["length",4]]]],[11,"extend_contents","","Appends `bytes` to the end of the DER contents to be build.",6,[[]]],[11,"finish","","Consumes `self` , building a new `Ber` instance.",6,[[],["ber",3]]],[0,"contents","","Provides functions to serialize/deserialize contents octets.",null,null],[5,"from_integer","bsn1::contents","Serializes integer as contents octets.",null,[[]]],[5,"to_integer","","Parses `bytes` as a contents of Integer.",null,[[],[["error",4],["result",4]]]],[5,"from_bool","","Serializes boolean as contents octets.",null,[[]]],[5,"to_bool_ber","","Parses `bytes` as a BER contents of Bool.",null,[[],[["result",4],["error",4]]]],[5,"to_bool_der","","Parses `bytes` as a DER contents of Bool.",null,[[],[["result",4],["error",4]]]],[11,"from_bytes_unchecked","bsn1","Provides a reference from `bytes` without any sanitization.",7,[[]]],[11,"from_bytes_starts_with_unchecked","","Provides a reference from `bytes` that starts with a DER.",7,[[]]],[11,"id","","Returns a reference to `IdRef` of `self` .",7,[[],["idref",3]]],[11,"length","","Returns `Length` to represent the length of contents.",7,[[],["length",4]]],[11,"contents","","Returns a reference to \'contents octets\' of `self` .",7,[[]]],[11,"new","","Creates a new instance from `id` and `contents` .",8,[[["idref",3]]]],[11,"new","","Creates a new instance to build `Der` with `id` and…",9,[[["idref",3],["length",4]]]],[11,"extend_contents","","Appends `bytes` to the end of the DER contents to be build.",9,[[]]],[11,"finish","","Consumes `self` , building a new `Der` .",9,[[],["der",3]]],[11,"from_bytes_unchecked","","Builds instance from `bytes` without any sanitize. `bytes`…",10,[[]]],[11,"eoc","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"boolean","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"integer","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"bit_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"bit_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"octet_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"octet_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"null","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"object_identifier","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"object_descriptor","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"external","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"real","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"enumerated","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"embedded_pdv","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"utf8_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"utf8_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"relative_oid","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"sequence","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"set","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"numeric_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"numeric_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"printable_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"printable_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"t61_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"t61_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"videotex_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"videotex_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"ia5_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"ia5_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"utc_time","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"utc_time_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"generalized_time","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"generalized_time_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"graphic_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"graphic_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"visible_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"visible_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"general_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"general_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"universal_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"universal_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"character_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"character_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"bmp_string","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"bmp_string_constructed","","Provides a reference to `IdRef` representing \'Universal…",10,[[]]],[11,"class","","Returns `ClassTag` of `self` .",10,[[],["classtag",4]]],[11,"is_universal","","Returns `true` if `self` is \'Universal\' class, or `false` .",10,[[]]],[11,"is_application","","Returns `true` if `self` is \'Application\' class, or…",10,[[]]],[11,"is_context_specific","","Returns `true` if `self` is \'Context Specific\' class, or…",10,[[]]],[11,"is_private","","Returns `true` if `self` is \'Private\' class, or `false` .",10,[[]]],[11,"pc","","Returns the Primitive/Constructed flag of `self` .",10,[[],["pctag",4]]],[11,"is_primitive","","Returns `true` if `self` is flagged as \'Primitive\', or…",10,[[]]],[11,"is_constructed","","Returns `true` if `self` is flagged as \'Constructed\', or…",10,[[]]],[11,"number","","Returns the number of `self` unless overflow.",10,[[],[["result",4],["error",4]]]],[11,"new","","Creates a new instance from `class` , `pc` , and `number` .",11,[[["pctag",4],["classtag",4]]]],[14,"constructed_ber","","Builds a `Ber` instance representing Constructed BER…",null,null],[14,"constructed_der","","Builds a `Der` instance representing \'Constructed DER\'…",null,null],[11,"from","","",5,[[]]],[11,"into","","",5,[[]]],[11,"to_owned","","",5,[[]]],[11,"clone_into","","",5,[[]]],[11,"borrow","","",5,[[]]],[11,"borrow_mut","","",5,[[]]],[11,"try_from","","",5,[[],["result",4]]],[11,"try_into","","",5,[[],["result",4]]],[11,"type_id","","",5,[[],["typeid",3]]],[11,"from","","",6,[[]]],[11,"into","","",6,[[]]],[11,"borrow","","",6,[[]]],[11,"borrow_mut","","",6,[[]]],[11,"try_from","","",6,[[],["result",4]]],[11,"try_into","","",6,[[],["result",4]]],[11,"type_id","","",6,[[],["typeid",3]]],[11,"to_owned","","",4,[[]]],[11,"clone_into","","",4,[[]]],[11,"borrow","","",4,[[]]],[11,"borrow_mut","","",4,[[]]],[11,"type_id","","",4,[[],["typeid",3]]],[11,"from","","",8,[[]]],[11,"into","","",8,[[]]],[11,"to_owned","","",8,[[]]],[11,"clone_into","","",8,[[]]],[11,"borrow","","",8,[[]]],[11,"borrow_mut","","",8,[[]]],[11,"try_from","","",8,[[],["result",4]]],[11,"try_into","","",8,[[],["result",4]]],[11,"type_id","","",8,[[],["typeid",3]]],[11,"from","","",9,[[]]],[11,"into","","",9,[[]]],[11,"borrow","","",9,[[]]],[11,"borrow_mut","","",9,[[]]],[11,"try_from","","",9,[[],["result",4]]],[11,"try_into","","",9,[[],["result",4]]],[11,"type_id","","",9,[[],["typeid",3]]],[11,"to_owned","","",7,[[]]],[11,"clone_into","","",7,[[]]],[11,"borrow","","",7,[[]]],[11,"borrow_mut","","",7,[[]]],[11,"type_id","","",7,[[],["typeid",3]]],[11,"from","","",11,[[]]],[11,"into","","",11,[[]]],[11,"to_owned","","",11,[[]]],[11,"clone_into","","",11,[[]]],[11,"borrow","","",11,[[]]],[11,"borrow_mut","","",11,[[]]],[11,"try_from","","",11,[[],["result",4]]],[11,"try_into","","",11,[[],["result",4]]],[11,"type_id","","",11,[[],["typeid",3]]],[11,"to_owned","","",10,[[]]],[11,"clone_into","","",10,[[]]],[11,"borrow","","",10,[[]]],[11,"borrow_mut","","",10,[[]]],[11,"type_id","","",10,[[],["typeid",3]]],[11,"from","","",0,[[]]],[11,"into","","",0,[[]]],[11,"to_owned","","",0,[[]]],[11,"clone_into","","",0,[[]]],[11,"borrow","","",0,[[]]],[11,"borrow_mut","","",0,[[]]],[11,"try_from","","",0,[[],["result",4]]],[11,"try_into","","",0,[[],["result",4]]],[11,"type_id","","",0,[[],["typeid",3]]],[11,"from","","",1,[[]]],[11,"into","","",1,[[]]],[11,"to_owned","","",1,[[]]],[11,"clone_into","","",1,[[]]],[11,"borrow","","",1,[[]]],[11,"borrow_mut","","",1,[[]]],[11,"try_from","","",1,[[],["result",4]]],[11,"try_into","","",1,[[],["result",4]]],[11,"type_id","","",1,[[],["typeid",3]]],[11,"from","","",2,[[]]],[11,"into","","",2,[[]]],[11,"to_owned","","",2,[[]]],[11,"clone_into","","",2,[[]]],[11,"borrow","","",2,[[]]],[11,"borrow_mut","","",2,[[]]],[11,"try_from","","",2,[[],["result",4]]],[11,"try_into","","",2,[[],["result",4]]],[11,"type_id","","",2,[[],["typeid",3]]],[11,"from","","",3,[[]]],[11,"into","","",3,[[]]],[11,"to_owned","","",3,[[]]],[11,"clone_into","","",3,[[]]],[11,"to_string","","",3,[[],["string",3]]],[11,"borrow","","",3,[[]]],[11,"borrow_mut","","",3,[[]]],[11,"try_from","","",3,[[],["result",4]]],[11,"try_into","","",3,[[],["result",4]]],[11,"type_id","","",3,[[],["typeid",3]]],[11,"as_ref","","",4,[[]]],[11,"as_ref","","",5,[[]]],[11,"as_ref","","",5,[[],["berref",3]]],[11,"as_ref","","",7,[[]]],[11,"as_ref","","",8,[[]]],[11,"as_ref","","",8,[[],["derref",3]]],[11,"as_ref","","",10,[[]]],[11,"as_ref","","",11,[[]]],[11,"as_ref","","",11,[[],["idref",3]]],[11,"from","","",5,[[["derref",3]]]],[11,"from","","",5,[[["der",3]]]],[11,"from","","",5,[[["berref",3]]]],[11,"from","","",8,[[["derref",3]]]],[11,"clone","","",5,[[],["ber",3]]],[11,"clone","","",8,[[],["der",3]]],[11,"clone","","",0,[[],["classtag",4]]],[11,"clone","","",1,[[],["pctag",4]]],[11,"clone","","",11,[[],["id",3]]],[11,"clone","","",2,[[],["length",4]]],[11,"clone","","",3,[[],["error",4]]],[11,"cmp","","",0,[[["classtag",4]],["ordering",4]]],[11,"cmp","","",1,[[["pctag",4]],["ordering",4]]],[11,"cmp","","",10,[[["idref",3]],["ordering",4]]],[11,"cmp","","",11,[[["id",3]],["ordering",4]]],[11,"eq","","",4,[[["berref",3]]]],[11,"ne","","",4,[[["berref",3]]]],[11,"eq","","",5,[[["ber",3]]]],[11,"ne","","",5,[[["ber",3]]]],[11,"eq","","",7,[[["derref",3]]]],[11,"ne","","",7,[[["derref",3]]]],[11,"eq","","",8,[[["der",3]]]],[11,"ne","","",8,[[["der",3]]]],[11,"eq","","",0,[[["classtag",4]]]],[11,"eq","","",1,[[["pctag",4]]]],[11,"eq","","",10,[[["idref",3]]]],[11,"ne","","",10,[[["idref",3]]]],[11,"eq","","",11,[[["id",3]]]],[11,"ne","","",11,[[["id",3]]]],[11,"eq","","",2,[[["length",4]]]],[11,"ne","","",2,[[["length",4]]]],[11,"eq","","",3,[[["error",4]]]],[11,"partial_cmp","","",0,[[["classtag",4]],[["ordering",4],["option",4]]]],[11,"partial_cmp","","",1,[[["pctag",4]],[["ordering",4],["option",4]]]],[11,"partial_cmp","","",10,[[["idref",3]],[["ordering",4],["option",4]]]],[11,"lt","","",10,[[["idref",3]]]],[11,"le","","",10,[[["idref",3]]]],[11,"gt","","",10,[[["idref",3]]]],[11,"ge","","",10,[[["idref",3]]]],[11,"partial_cmp","","",11,[[["id",3]],[["ordering",4],["option",4]]]],[11,"lt","","",11,[[["id",3]]]],[11,"le","","",11,[[["id",3]]]],[11,"gt","","",11,[[["id",3]]]],[11,"ge","","",11,[[["id",3]]]],[11,"to_owned","","",4,[[]]],[11,"to_owned","","",7,[[]]],[11,"to_owned","","",10,[[]]],[11,"deref","","",5,[[]]],[11,"deref","","",8,[[]]],[11,"deref","","",11,[[]]],[11,"fmt","","",4,[[["formatter",3]],["result",6]]],[11,"fmt","","",5,[[["formatter",3]],["result",6]]],[11,"fmt","","",7,[[["formatter",3]],["result",6]]],[11,"fmt","","",8,[[["formatter",3]],["result",6]]],[11,"fmt","","",0,[[["formatter",3]],["result",6]]],[11,"fmt","","",1,[[["formatter",3]],["result",6]]],[11,"fmt","","",10,[[["formatter",3]],["result",6]]],[11,"fmt","","",11,[[["formatter",3]],["result",6]]],[11,"fmt","","",2,[[["formatter",3]],["result",6]]],[11,"fmt","","",3,[[["formatter",3]],["result",6]]],[11,"fmt","","",3,[[["formatter",3]],["result",6]]],[11,"hash","","",0,[[]]],[11,"hash","","",1,[[]]],[11,"hash","","",10,[[]]],[11,"hash","","",11,[[]]],[11,"hash","","",2,[[]]],[11,"hash","","",3,[[]]],[11,"borrow","","",4,[[]]],[11,"borrow","","",5,[[]]],[11,"borrow","","",5,[[],["berref",3]]],[11,"borrow","","",7,[[]]],[11,"borrow","","",8,[[]]],[11,"borrow","","",8,[[],["derref",3]]],[11,"borrow","","",10,[[]]],[11,"borrow","","",11,[[]]],[11,"borrow","","",11,[[],["idref",3]]],[11,"try_from","","Parses `bytes` starting with octets of \'ASN.1 BER\' and…",5,[[],["result",4]]],[11,"try_from","","Parses `bytes` starting with DER octets and builds a new…",8,[[],["result",4]]],[11,"try_from","","Parses `bytes` starts with identifier octets and tries to…",11,[[],["result",4]]]],"p":[[4,"ClassTag"],[4,"PCTag"],[4,"Length"],[4,"Error"],[3,"BerRef"],[3,"Ber"],[3,"BerBuilder"],[3,"DerRef"],[3,"Der"],[3,"DerBuilder"],[3,"IdRef"],[3,"Id"]]}\
}');
addSearchOptions(searchIndex);initSearch(searchIndex);