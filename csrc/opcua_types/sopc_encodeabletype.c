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

    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        field_desc = &enc_type->Descriptor->Elements[i];

        field_ptr = ((char*) pValue) + field_desc->Offset;

        if (field_desc->IsArray)
        {
            nbelem_ptr = ((char*) pValue) + field_desc->OffsetNbElem;

            if (field_desc->IsBuiltIn)
            {
                allocation_size = SOPC_GetBuiltinSize(field_desc->Type.BuiltInId);
                init_fctn = SOPC_GetBuiltInTypeInitializeFunction(field_desc->Type.BuiltInId);
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
                init_fctn = SOPC_GetBuiltInTypeInitializeFunction(field_desc->Type.BuiltInId);
                init_fctn(field_ptr);
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
    void* field_ptr = NULL;
    void* nbelem_ptr = NULL;
    SOPC_FieldDescriptor* field_desc = NULL;

    size_t allocation_size;
    SOPC_EncodeableObject_PfnClear* clear_fctn = NULL;

    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        field_desc = &enc_type->Descriptor->Elements[i];

        field_ptr = ((char*) pValue) + field_desc->Offset;

        if (field_desc->IsArray)
        {
            nbelem_ptr = ((char*) pValue) + field_desc->OffsetNbElem;

            if (field_desc->IsBuiltIn)
            {
                allocation_size = SOPC_GetBuiltinSize(field_desc->Type.BuiltInId);
                clear_fctn = SOPC_GetBuiltInTypeClearFunction(field_desc->Type.BuiltInId);
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
                clear_fctn = SOPC_GetBuiltInTypeClearFunction(field_desc->Type.BuiltInId);
                clear_fctn(field_ptr);
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

    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        if (SOPC_STATUS_OK == status)
        {
            field_desc = &enc_type->Descriptor->Elements[i];

            const void* field_ptr = ((const char*) pValue) + field_desc->Offset;

            if (field_desc->IsArray)
            {
                if (field_desc->IsBuiltIn)
                {
                    allocation_size = SOPC_GetBuiltinSize(field_desc->Type.BuiltInId);
                    write_fctn = SOPC_GetBuiltInTypeWriteFunction(field_desc->Type.BuiltInId);
                }
                else
                {
                    allocation_size = field_desc->Type.NestedEncType->AllocationSize;
                    write_fctn = (SOPC_EncodeableObject_PfnEncode*) field_desc->Type.NestedEncType->Encode;
                }

                const void* nbelem_ptr = ((const char*) pValue) + field_desc->OffsetNbElem;

                const void* const* array_ptr = field_ptr;
                
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
                    write_fctn = SOPC_GetBuiltInTypeWriteFunction(field_desc->Type.BuiltInId);
                    status = write_fctn(field_ptr, buf);
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

    void* field_ptr = NULL;
    void* nbelem_ptr = NULL;

    if (pValue != NULL && buf != NULL)
    {
        status = SOPC_STATUS_OK;
    }

    SOPC_Generic_Initialize(pValue, enc_type);

    for (uint32_t i = 0 ; i < enc_type->Descriptor->nbElements ; i++)
    {
        if (SOPC_STATUS_OK == status)
        {
            field_desc = &enc_type->Descriptor->Elements[i];

            field_ptr = ((char*) pValue) + field_desc->Offset;

            if (field_desc->IsArray)
            {
                nbelem_ptr = ((char*) pValue) + field_desc->OffsetNbElem;

                if (field_desc->IsBuiltIn)
                {
                    allocation_size = SOPC_GetBuiltinSize(field_desc->Type.BuiltInId);
                    read_fctn = SOPC_GetBuiltInTypeReadFunction(field_desc->Type.BuiltInId);
                    init_fctn = SOPC_GetBuiltInTypeInitializeFunction(field_desc->Type.BuiltInId);
                    clear_fctn = SOPC_GetBuiltInTypeClearFunction(field_desc->Type.BuiltInId);
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
                    read_fctn = SOPC_GetBuiltInTypeReadFunction(field_desc->Type.BuiltInId);
                    status = read_fctn(field_ptr, buf);
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