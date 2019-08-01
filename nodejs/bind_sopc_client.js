const ffi = require('ffi');
const ref = require('ref');
const StructType = require('ref-struct');
const ArrayType = require('ref-array');
const UnionType = require('ref-union');
const Enum = require('enum');

const CStringArray = ArrayType(ref.types.CString);

const SOPC_ClientHelper_SecurityCfg = StructType({
    security_policy: 'CString',
    security_mode: 'int32',
    path_cert_auth: 'CString',
    path_cert_srv: 'CString',
    path_cert_cli: 'CString',
    path_key_cli: 'CString',
    policyId: 'CString',
    username: 'CString',
    password: 'CString'
});

const SOPC_BuiltinId = new Enum({
    'SOPC_Null_Id': 0,
    'SOPC_Boolean_Id': 1,
    'SOPC_SByte_Id': 2,
    'SOPC_Byte_Id': 3,
    'SOPC_Int16_Id': 4,
    'SOPC_UInt16_Id': 5,
    'SOPC_Int32_Id': 6,
    'SOPC_UInt32_Id': 7,
    'SOPC_Int64_Id': 8,
    'SOPC_UInt64_Id': 9,
    'SOPC_Float_Id': 10,
    'SOPC_Double_Id': 11,
    'SOPC_String_Id': 12,
    'SOPC_DateTime_Id': 13,
    'SOPC_Guid_Id': 14,
    'SOPC_ByteString_Id': 15,
    'SOPC_XmlElement_Id': 16,
    'SOPC_NodeId_Id': 17,
    'SOPC_ExpandedNodeId_Id': 18,
    'SOPC_StatusCode_Id': 19,
    'SOPC_QualifiedName_Id': 20,
    'SOPC_LocalizedText_Id': 21,
    'SOPC_ExtensionObject_Id': 22,
    'SOPC_DataValue_Id': 23,
    'SOPC_Variant_Id': 24,
    'SOPC_DiagnosticInfo_Id': 25
});

const SOPC_VariantArrayType = new Enum({
    'SOPC_VariantArrayType_SingleValue': 0,
    'SOPC_VariantArrayType_Array': 1,
    'SOPC_VariantArrayType_Matrix': 2,
});

const uint8_ptr = ref.refType('uint8');

const SOPC_String = StructType({
    length: 'int32',
    do_not_clear: 'bool',
    data: uint8_ptr
});

const SOPC_Guid = StructType({
    data1: 'uint32',
    data2: 'uint16',
    data3: 'uint16',
    data4: uint8_ptr
});

const SOPC_GuidPtr = ref.refType(SOPC_Guid);

const SOPC_IdentifierType = new Enum({
    'SOPC_IdentifierType_Numeric': 0,
    'SOPC_IdentifierType_String': 1,
    'SOPC_IdentifierType_Guid': 2,
    'SOPC_IdentifierType_ByteString': 3,
});

const SOPC_NodeIdData = UnionType({
    numeric: 'uint32',
    string : SOPC_String,
    guid : SOPC_GuidPtr,
    bstring : SOPC_String
});

const SOPC_NodeId = StructType({
    id_type : SOPC_IdentifierType,
    ns : 'uint16',
    data : SOPC_NodeIdData
});

const SOPC_VariantValue = UnionType({
    bool: 'bool',
    sbyte: 'int8',
    bytev: 'uint8',
    int16: 'int16',
    uint16: 'uint16',
    int32: 'int32',
    uint32: 'uint32',
    int64: 'int64',
    uint64: 'uint64',
    floatv: 'float',
    doublev: 'double',
    string: SOPC_String,
    date_time: 'int64',
    guid: SOPC_GuidPtr,
    bstring: SOPC_String,
    xml_elt: SOPC_String,
    node_id: SOPC_NodeIdPtr,
    exp_node_id: SOPC_ExpandedNodeIdPtr,
    status: 'uint32',
    qname: SOPC_QualifiedNamePtr,
    localized_text: SOPC_LocalizedTextPtr,
    extension_obj: SOPC_ExtensionObjectPtr,
    data_value: SOPC_DataValuePtr,
    diag_info: SOPC_DiagnosticInfoPtr,
    array: SOPC_VariantArray,
    matrix: SOPC_VariantMatrix
});

const SOPC_Variant = StructType({
    do_not_clear: 'bool',
    built_in_type_id: SOPC_BuiltinId,
    variant_array_type: SOPC_VariantArrayType,
    variant_value: SOPC_VariantValue
});

const SOPC_DataValue = StructType({
    value: SOPC_Variant,
    status: 'uint32',
    src_ts: 'int64',
    srv_ts: 'int64',
    src_ps: 'uint16',
    srv_ps: 'uint16'
});

const SOPC_ClientHelper_WriteValue = StructType({
    nodeId: 'CString',
    indexRange: 'CString',
    dataValue: SOPC_DataValue,
    path_cert_auth: 'CString',
    path_cert_srv: 'CString',
    path_cert_cli: 'CString',
    path_key_cli: 'CString',
    policyId: 'CString',
    username: 'CString',
    password: 'CString'
});

const sopc_client = ffi.Library('libclient_subscription', {
    'SOPC_ClientHelper_Initialize': ['int32', ['CString', 'int32']],
    'SOPC_ClientHelper_Finalize': ['void', []],
    'SOPC_ClientHelper_Connect': ['int32', ['CString', SOPC_ClientHelper_SecurityCfg]],
    'SOPC_ClientHelper_Disconnect': ['int32', ['int32']],
    'SOPC_ClientHelper_CreateSubscribtion': ['int32', ['int32', 'pointer']],
    'SOPC_ClientHelper_AddMonitoredItems': ['int32', [CStringArray, 'size_t']],
    'SOPC_ClientHelper_Unsubscribe': ['int32', ['int32']],
    'SOPC_ClientHelper_Write': ['int32', ['int32', ]]
});

module.exports.sopc_client = sopc_client
module.exports.CStringArray = CStringArray

