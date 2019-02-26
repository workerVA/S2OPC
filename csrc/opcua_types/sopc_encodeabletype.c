/*
 * Licensed to Systerel under one or more contributor license
 * agreements. See the NOTICE file distributed with this work
 * for additional information regarding copyright ownership.
 * Systerel licenses this file to you under the Apache
 * License, Version 2.0 (the "License"); you may not use this
 * file except in compliance with the License. You may obtain
 * a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

#include "sopc_encodeabletype.h"
#include "sopc_encoder.h"
#include "sopc_macros.h"

#include <string.h>

#include "sopc_builtintypes.h"
#include "sopc_helper_string.h"
#include "sopc_types.h"
#include <assert.h>

const char* nullType = "NULL";
const char* noNameType = "NoName";

SOPC_EncodeableType* SOPC_EncodeableType_GetEncodeableType(uint32_t typeId)
{
    SOPC_EncodeableType* current = NULL;
    SOPC_EncodeableType* result = NULL;
    uint32_t idx = 0;
    current = SOPC_KnownEncodeableTypes[idx];
    while (current != NULL && NULL == result)
    {
        if (typeId == current->TypeId || typeId == current->BinaryEncodingTypeId)
        {
            result = current;
        }
        if (NULL == result && idx < UINT32_MAX)
        {
            idx++;
            current = SOPC_KnownEncodeableTypes[idx];
        }
        else
        {
            current = NULL;
        }
    }
    return result;
}

const char* SOPC_EncodeableType_GetName(SOPC_EncodeableType* encType)
{
    const char* result = NULL;
    if (encType == NULL)
    {
        result = nullType;
    }
    else if (encType->TypeName == NULL)
    {
        result = noNameType;
    }
    else
    {
        result = encType->TypeName;
    }
    return result;
}

void (*init_aux_arr[SOPC_BUILTINID_MAX + 1])(void*) = {
    NULL,
    &SOPC_Boolean_InitializeAux,
    &SOPC_SByte_InitializeAux,
    &SOPC_Byte_InitializeAux,
    &SOPC_Int16_InitializeAux,
    &SOPC_UInt16_InitializeAux,
    &SOPC_Int32_InitializeAux,
    &SOPC_UInt32_InitializeAux,
    &SOPC_Int64_InitializeAux,
    &SOPC_UInt64_InitializeAux,
    &SOPC_Float_InitializeAux,
    &SOPC_Double_InitializeAux,
    &SOPC_String_InitializeAux,
    &SOPC_DateTime_InitializeAux,
    &SOPC_Guid_InitializeAux,
    &SOPC_ByteString_InitializeAux,
    &SOPC_XmlElement_InitializeAux,
    &SOPC_NodeId_InitializeAux,
    &SOPC_ExpandedNodeId_InitializeAux,
    &SOPC_StatusCode_InitializeAux,
    &SOPC_QualifiedName_InitializeAux,
    &SOPC_LocalizedText_InitializeAux,
    &SOPC_ExtensionObject_InitializeAux,
    &SOPC_DataValue_InitializeAux,
    &SOPC_Variant_InitializeAux,
    &SOPC_DiagnosticInfo_InitializeAux
};

void (*clear_aux_arr[SOPC_BUILTINID_MAX + 1])(void*) = {
    NULL,
    &SOPC_Boolean_ClearAux,
    &SOPC_SByte_ClearAux,
    &SOPC_Byte_ClearAux,
    &SOPC_Int16_ClearAux,
    &SOPC_UInt16_ClearAux,
    &SOPC_Int32_ClearAux,
    &SOPC_UInt32_ClearAux,
    &SOPC_Int64_ClearAux,
    &SOPC_UInt64_ClearAux,
    &SOPC_Float_ClearAux,
    &SOPC_Double_ClearAux,
    &SOPC_String_ClearAux,
    &SOPC_DateTime_ClearAux,
    &SOPC_Guid_ClearAux,
    &SOPC_ByteString_ClearAux,
    &SOPC_XmlElement_ClearAux,
    &SOPC_NodeId_ClearAux,
    &SOPC_ExpandedNodeId_ClearAux,
    &SOPC_StatusCode_ClearAux,
    &SOPC_QualifiedName_ClearAux,
    &SOPC_LocalizedText_ClearAux,
    &SOPC_ExtensionObject_ClearAux,
    &SOPC_DataValue_ClearAux,
    &SOPC_Variant_ClearAux,
    &SOPC_DiagnosticInfo_ClearAux
};

SOPC_ReturnStatus (*write_aux_arr[SOPC_BUILTINID_MAX + 1])(const void*, SOPC_Buffer*) = {
    NULL,
    &SOPC_Boolean_WriteAux,
    &SOPC_SByte_WriteAux,
    &SOPC_Byte_WriteAux,
    &SOPC_Int16_WriteAux,
    &SOPC_UInt16_WriteAux,
    &SOPC_Int32_WriteAux,
    &SOPC_UInt32_WriteAux,
    &SOPC_Int64_WriteAux,
    &SOPC_UInt64_WriteAux,
    &SOPC_Float_WriteAux,
    &SOPC_Double_WriteAux,
    &SOPC_String_WriteAux,
    &SOPC_DateTime_WriteAux,
    &SOPC_Guid_WriteAux,
    &SOPC_ByteString_WriteAux,
    &SOPC_XmlElement_WriteAux,
    &SOPC_NodeId_WriteAux,
    &SOPC_ExpandedNodeId_WriteAux,
    &SOPC_StatusCode_WriteAux,
    &SOPC_QualifiedName_WriteAux,
    &SOPC_LocalizedText_WriteAux,
    &SOPC_ExtensionObject_WriteAux,
    &SOPC_DataValue_WriteAux,
    &SOPC_Variant_WriteAux,
    &SOPC_DiagnosticInfo_WriteAux
};

SOPC_ReturnStatus (*read_aux_arr[SOPC_BUILTINID_MAX + 1])(void*, SOPC_Buffer*) = {
    NULL,
    &SOPC_Boolean_ReadAux,
    &SOPC_SByte_ReadAux,
    &SOPC_Byte_ReadAux,
    &SOPC_Int16_ReadAux,
    &SOPC_UInt16_ReadAux,
    &SOPC_Int32_ReadAux,
    &SOPC_UInt32_ReadAux,
    &SOPC_Int64_ReadAux,
    &SOPC_UInt64_ReadAux,
    &SOPC_Float_ReadAux,
    &SOPC_Double_ReadAux,
    &SOPC_String_ReadAux,
    &SOPC_DateTime_ReadAux,
    &SOPC_Guid_ReadAux,
    &SOPC_ByteString_ReadAux,
    &SOPC_XmlElement_ReadAux,
    &SOPC_NodeId_ReadAux,
    &SOPC_ExpandedNodeId_ReadAux,
    &SOPC_StatusCode_ReadAux,
    &SOPC_QualifiedName_ReadAux,
    &SOPC_LocalizedText_ReadAux,
    &SOPC_ExtensionObject_ReadAux,
    &SOPC_DataValue_ReadAux,
    &SOPC_Variant_ReadAux,
    &SOPC_DiagnosticInfo_ReadAux
};

size_t alloc_size_arr[SOPC_BUILTINID_MAX + 1] = {
    0,
    sizeof (SOPC_Boolean),
    sizeof (int8_t),
    sizeof (uint8_t),
    sizeof (int16_t),
    sizeof (uint16_t),
    sizeof (int32_t),
    sizeof (uint32_t),
    sizeof (int64_t),
    sizeof (uint64_t),
    sizeof (float),
    sizeof (double),
    sizeof (SOPC_ByteString),
    sizeof (SOPC_String),
    sizeof (SOPC_XmlElement),
    sizeof (SOPC_DateTime),
    sizeof (SOPC_Guid),
    sizeof (SOPC_NodeId),
    sizeof (SOPC_ExpandedNodeId),
    sizeof (SOPC_StatusCode),
    sizeof (SOPC_DiagnosticInfo),
    sizeof (SOPC_QualifiedName),
    sizeof (SOPC_LocalizedText),
    sizeof (SOPC_ExtensionObject),
    sizeof (SOPC_Variant),
    sizeof (SOPC_DataValue)
};


void SOPC_Generic_Initialize(void* pValue, SOPC_EncodeableType* enc_type)
{
    // Initializing encodeable type
    void* field_ptr = NULL;
    void* nbelem_ptr = NULL;

    size_t allocation_size;
    SOPC_EncodeableObject_PfnInitialize* init_fctn = NULL;

    SOPC_FieldDescriptor* field_desc = NULL;
    SOPC_EncodeableType** field_ec_type = (SOPC_EncodeableType**) pValue;
    *field_ec_type = enc_type;

    // Initializing fields
    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        // Getting the field
        field_desc = &enc_type->Descriptor->Elements[i];

        field_ptr = ((char*) pValue) + field_desc->Offset;

        if (field_desc->IsArray)
        {
            nbelem_ptr = ((char*) pValue) + field_desc->OffsetNbElem;

            if (field_desc->IsBuiltIn)
            {
                allocation_size = alloc_size_arr[field_desc->Type.BuiltInId];
                init_fctn = (SOPC_EncodeableObject_PfnInitialize*) init_aux_arr[field_desc->Type.BuiltInId];
            }
            else
            {
                allocation_size = field_desc->Type.NestedEncType->AllocationSize;
                init_fctn = (SOPC_EncodeableObject_PfnInitialize*) field_desc->Type.NestedEncType->Initialize;
            }

            SOPC_Initialize_Array(
                (int32_t*) nbelem_ptr,
                (void**) field_ptr,
                allocation_size,
                init_fctn);
        }
        else
        {
            if (field_desc->IsBuiltIn)
            {
                init_aux_arr[field_desc->Type.BuiltInId](field_ptr);
            }
            else
            {
                SOPC_Generic_Initialize(field_ptr, field_desc->Type.NestedEncType);
            }
        } 
    }
}

void SOPC_Generic_Clear(void* pValue, SOPC_EncodeableType* enc_type)
{
    // Initializing encodeable type
    void* field_ptr = NULL;
    void* nbelem_ptr = NULL;
    SOPC_FieldDescriptor* field_desc = NULL;

    size_t allocation_size;
    SOPC_EncodeableObject_PfnClear* clear_fctn = NULL;

    // Initializing fields
    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        // Getting the field
        field_desc = &enc_type->Descriptor->Elements[i];

        field_ptr = ((char*) pValue) + field_desc->Offset;

        if (field_desc->IsArray)
        {
            nbelem_ptr = ((char*) pValue) + field_desc->OffsetNbElem;

            if (field_desc->IsBuiltIn)
            {
                allocation_size = alloc_size_arr[field_desc->Type.BuiltInId];
                clear_fctn = (SOPC_EncodeableObject_PfnClear*) clear_aux_arr[field_desc->Type.BuiltInId];
            }
            else
            {
                allocation_size = field_desc->Type.NestedEncType->AllocationSize;
                clear_fctn = (SOPC_EncodeableObject_PfnClear*) field_desc->Type.NestedEncType->Clear;
            }

            SOPC_Clear_Array(
                (int32_t*) nbelem_ptr,
                (void**) field_ptr,
                allocation_size,
                clear_fctn);
        }
        else
        {
            if (field_desc->IsBuiltIn)
            {
                clear_aux_arr[field_desc->Type.BuiltInId](field_ptr);
            }
            else
            {
                SOPC_Generic_Clear(field_ptr, field_desc->Type.NestedEncType);
            }
        }
    }
}


SOPC_ReturnStatus SOPC_Generic_Encode(const void* pValue, SOPC_EncodeableType* enc_type, SOPC_Buffer* buf)
{
    SOPC_ReturnStatus status = SOPC_STATUS_INVALID_PARAMETERS;

    SOPC_FieldDescriptor* field_desc = NULL;

    size_t allocation_size;
    SOPC_EncodeableObject_PfnEncode* write_fctn = NULL;

    if (pValue != NULL && buf != NULL)
    {
        status = SOPC_STATUS_OK;
    }

    // Initializing fields
    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        if (SOPC_STATUS_OK == status)
        {
            // Getting the field
            field_desc = &enc_type->Descriptor->Elements[i];

            const void* field_ptr = ((const char*) pValue) + field_desc->Offset;

            if (field_desc->IsArray)
            {

                if (field_desc->IsBuiltIn)
                {
                    allocation_size = alloc_size_arr[field_desc->Type.BuiltInId];
                    write_fctn = (SOPC_EncodeableObject_PfnEncode*) write_aux_arr[field_desc->Type.BuiltInId];
                }
                else
                {
                    allocation_size = field_desc->Type.NestedEncType->AllocationSize;
                    write_fctn = (SOPC_EncodeableObject_PfnEncode*) field_desc->Type.NestedEncType->Encode;
                }

                const void* nbelem_ptr = ((const char*) pValue) + field_desc->OffsetNbElem;

                // Pointer containing address to array (cqfd void**)
                SOPC_GCC_DIAGNOSTIC_IGNORE_CAST_CONST
                const void** array_ptr = (const void**) field_ptr;
                SOPC_GCC_DIAGNOSTIC_RESTORE
                
                status = SOPC_Write_Array(
                    buf,
                    (const int32_t*) nbelem_ptr,
                    array_ptr,
                    allocation_size,
                    write_fctn);

            }
            else
            {
                if (field_desc->IsBuiltIn)
                {
                    status = write_aux_arr[field_desc->Type.BuiltInId](field_ptr, buf);
                }
                else
                {
                    status = SOPC_Generic_Encode(field_ptr, field_desc->Type.NestedEncType, buf);
                }
            }
        }
    }
    
    return status;
}


SOPC_ReturnStatus SOPC_Generic_Decode(void* pValue, SOPC_EncodeableType* enc_type, SOPC_Buffer* buf)
{
    SOPC_ReturnStatus status = SOPC_STATUS_INVALID_PARAMETERS;
    SOPC_FieldDescriptor* field_desc = NULL;

    size_t allocation_size;
    SOPC_EncodeableObject_PfnDecode* read_fctn = NULL;
    SOPC_EncodeableObject_PfnInitialize* init_fctn = NULL;
    SOPC_EncodeableObject_PfnClear* clear_fctn = NULL;

    // Initializing encodeable type
    void* field_ptr = NULL;
    void* nbelem_ptr = NULL;

    if (pValue != NULL && buf != NULL)
    {
        status = SOPC_STATUS_OK;
    }

    SOPC_Generic_Initialize(pValue, enc_type);

    // Initializing fields
    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        if (SOPC_STATUS_OK == status)
        {
            // Getting the field
            field_desc = &enc_type->Descriptor->Elements[i];

            field_ptr = ((char*) pValue) + field_desc->Offset;

            if (field_desc->IsArray)
            {
                nbelem_ptr = ((char*) pValue) + field_desc->OffsetNbElem;

                if (field_desc->IsBuiltIn)
                {
                    allocation_size = alloc_size_arr[field_desc->Type.BuiltInId];
                    read_fctn = (SOPC_EncodeableObject_PfnDecode*) read_aux_arr[field_desc->Type.BuiltInId];
                    init_fctn = (SOPC_EncodeableObject_PfnInitialize*) init_aux_arr[field_desc->Type.BuiltInId];
                    clear_fctn = (SOPC_EncodeableObject_PfnClear*) clear_aux_arr[field_desc->Type.BuiltInId];
                }
                else
                {
                    allocation_size = field_desc->Type.NestedEncType->AllocationSize;
                    read_fctn = (SOPC_EncodeableObject_PfnDecode*) field_desc->Type.NestedEncType->Decode;
                    init_fctn = (SOPC_EncodeableObject_PfnInitialize*) field_desc->Type.NestedEncType->Initialize;
                    clear_fctn = (SOPC_EncodeableObject_PfnClear*) field_desc->Type.NestedEncType->Clear;
                }

                status = SOPC_Read_Array(
                        buf,
                        (int32_t*) nbelem_ptr,
                        (void**) field_ptr,
                        allocation_size,
                        read_fctn,
                        init_fctn,
                        clear_fctn);
            }
            else
            {
                if (field_desc->IsBuiltIn)
                {
                    status = read_aux_arr[field_desc->Type.BuiltInId](field_ptr, buf);
                }
                else
                {
                    status = SOPC_Generic_Decode(field_ptr, field_desc->Type.NestedEncType, buf);
                }
            }
        }
    }

    if (status != SOPC_STATUS_OK && pValue != NULL)
    {
        SOPC_Generic_Clear(pValue, enc_type);
    }
    
    return status;
}