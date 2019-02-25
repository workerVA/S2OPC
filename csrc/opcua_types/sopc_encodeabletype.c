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
                switch(field_desc->Type.BuiltInId)
                {
                    case SOPC_Boolean_Id:
                        allocation_size = sizeof (SOPC_Boolean);
                        init_fctn = &SOPC_Boolean_InitializeAux;
                        break;
                    case SOPC_SByte_Id:
                        allocation_size = sizeof (int8_t);
                        init_fctn = &SOPC_SByte_InitializeAux;
                        break;
                    case SOPC_Byte_Id:
                        allocation_size = sizeof (uint8_t);
                        init_fctn = &SOPC_Byte_InitializeAux;
                        break;
                    case SOPC_Int16_Id:
                        allocation_size = sizeof (int16_t);
                        init_fctn = &SOPC_Int16_InitializeAux;
                        break;
                    case SOPC_Int32_Id:
                        allocation_size = sizeof (int32_t);
                        init_fctn = &SOPC_Int32_InitializeAux;
                        break;
                    case SOPC_UInt32_Id:
                        allocation_size = sizeof (uint32_t);
                        init_fctn = &SOPC_UInt32_InitializeAux;
                        break;
                    case SOPC_Double_Id:
                        allocation_size = sizeof (double);
                        init_fctn = &SOPC_Double_InitializeAux;
                        break;
                    case SOPC_DateTime_Id:
                        allocation_size = sizeof (SOPC_DateTime);
                        init_fctn = &SOPC_DateTime_InitializeAux;
                        break;
                    case SOPC_NodeId_Id:
                        allocation_size = sizeof (SOPC_NodeId);
                        init_fctn = &SOPC_NodeId_InitializeAux;
                        break;
                    case SOPC_QualifiedName_Id:
                        allocation_size = sizeof (SOPC_QualifiedName);
                        init_fctn = &SOPC_QualifiedName_InitializeAux;
                        break;
                    default:
                        assert(false);
                }
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
                switch(field_desc->Type.BuiltInId)
                {
                    case SOPC_Boolean_Id:
                        SOPC_Boolean_Initialize(field_ptr);
                        break;
                    case SOPC_SByte_Id:
                        SOPC_SByte_Initialize(field_ptr);
                        break;
                    case SOPC_Byte_Id:
                        SOPC_Byte_Initialize(field_ptr);
                        break;
                    case SOPC_Int16_Id:
                        SOPC_Int16_Initialize(field_ptr);
                        break;
                    case SOPC_Int32_Id:
                        SOPC_Int32_Initialize(field_ptr);
                        break;
                    case SOPC_UInt32_Id:
                        SOPC_UInt32_Initialize(field_ptr);
                        break;
                    case SOPC_Double_Id:
                        SOPC_Double_Initialize(field_ptr);
                        break;
                    case SOPC_DateTime_Id:
                        SOPC_DateTime_Initialize(field_ptr);
                        break;
                    case SOPC_NodeId_Id:
                        SOPC_NodeId_Initialize(field_ptr);
                        break;
                    case SOPC_QualifiedName_Id:
                        SOPC_QualifiedName_Initialize(field_ptr);
                        break;
                    default:
                        assert(false);
                }
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
                switch(field_desc->Type.BuiltInId)
                {
                    case SOPC_Boolean_Id:
                        allocation_size = sizeof (SOPC_Boolean);
                        clear_fctn = &SOPC_Boolean_ClearAux;
                        break;
                    case SOPC_SByte_Id:
                        allocation_size = sizeof (int8_t);
                        clear_fctn = &SOPC_SByte_ClearAux;
                        break;
                    case SOPC_Byte_Id:
                        allocation_size = sizeof (uint8_t);
                        clear_fctn = &SOPC_Byte_ClearAux;
                        break;
                    case SOPC_Int16_Id:
                        allocation_size = sizeof (int16_t);
                        clear_fctn = &SOPC_Int16_ClearAux;
                        break;
                    case SOPC_Int32_Id:
                        allocation_size = sizeof (int32_t);
                        clear_fctn = &SOPC_Int32_ClearAux;
                        break;
                    case SOPC_UInt32_Id:
                        allocation_size = sizeof (uint32_t);
                        clear_fctn = &SOPC_UInt32_ClearAux;
                        break;
                    case SOPC_Double_Id:
                        allocation_size = sizeof (double);
                        clear_fctn = &SOPC_Double_ClearAux;
                        break;
                    case SOPC_DateTime_Id:
                        allocation_size = sizeof (SOPC_DateTime);
                        clear_fctn = &SOPC_DateTime_ClearAux;
                        break;
                    case SOPC_NodeId_Id:
                        allocation_size = sizeof (SOPC_NodeId);
                        clear_fctn = &SOPC_NodeId_ClearAux;
                        break;
                    case SOPC_QualifiedName_Id:
                        allocation_size = sizeof (SOPC_QualifiedName);
                        clear_fctn = &SOPC_QualifiedName_ClearAux;
                        break;
                    default:
                        assert(false);
                }
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
                switch(field_desc->Type.BuiltInId)
                {
                    case SOPC_Boolean_Id:
                        SOPC_Boolean_Clear(field_ptr);
                        break;
                    case SOPC_SByte_Id:
                        SOPC_SByte_Clear(field_ptr);
                        break;
                    case SOPC_Byte_Id:
                        SOPC_Byte_Clear(field_ptr);
                        break;
                    case SOPC_Int16_Id:
                        SOPC_Int16_Clear(field_ptr);
                        break;
                    case SOPC_Int32_Id:
                        SOPC_Int32_Clear(field_ptr);
                        break;
                    case SOPC_UInt32_Id:
                        SOPC_UInt32_Clear(field_ptr);
                        break;
                    case SOPC_Double_Id:
                        SOPC_Double_Clear(field_ptr);
                        break;
                    case SOPC_DateTime_Id:
                        SOPC_DateTime_Clear(field_ptr);
                        break;
                    case SOPC_NodeId_Id:
                        SOPC_NodeId_Clear(field_ptr);
                        break;
                    case SOPC_QualifiedName_Id:
                        SOPC_QualifiedName_Clear(field_ptr);
                        break;
                    default:
                        assert(false);
                }
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
                    switch(field_desc->Type.BuiltInId)
                    {
                        case SOPC_Boolean_Id:
                            allocation_size = sizeof (SOPC_Boolean);
                            write_fctn = &SOPC_Boolean_WriteAux;
                            break;
                        case SOPC_SByte_Id:
                            allocation_size = sizeof (int8_t);
                            write_fctn = &SOPC_SByte_WriteAux;
                            break;
                        case SOPC_Byte_Id:
                            allocation_size = sizeof (uint8_t);
                            write_fctn = &SOPC_Byte_WriteAux;
                            break;
                        case SOPC_Int16_Id:
                            allocation_size = sizeof (int16_t);
                            write_fctn = &SOPC_Int16_WriteAux;
                            break;
                        case SOPC_Int32_Id:
                            allocation_size = sizeof (int32_t);
                            write_fctn = &SOPC_Int32_WriteAux;
                            break;
                        case SOPC_UInt32_Id:
                            allocation_size = sizeof (uint32_t);
                            write_fctn = &SOPC_UInt32_WriteAux;
                            break;
                        case SOPC_Double_Id:
                            allocation_size = sizeof (double);
                            write_fctn = &SOPC_Double_WriteAux;
                            break;
                        case SOPC_DateTime_Id:
                            allocation_size = sizeof (SOPC_DateTime);
                            write_fctn = &SOPC_DateTime_WriteAux;
                            break;
                        case SOPC_NodeId_Id:
                            allocation_size = sizeof (SOPC_NodeId);
                            write_fctn = &SOPC_NodeId_WriteAux;
                            break;
                        case SOPC_QualifiedName_Id:
                            allocation_size = sizeof (SOPC_QualifiedName);
                            write_fctn = &SOPC_QualifiedName_WriteAux;
                            break;
                        default:
                            assert(false);
                    }
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
                    switch(field_desc->Type.BuiltInId)
                    {
                        case SOPC_Boolean_Id:
                            status = SOPC_Boolean_Write(field_ptr, buf);
                            break;
                        case SOPC_SByte_Id:
                            status = SOPC_SByte_Write(field_ptr, buf);
                            break;
                        case SOPC_Byte_Id:
                            status = SOPC_Byte_Write(field_ptr, buf);
                            break;
                        case SOPC_Int16_Id:
                            status = SOPC_Int16_Write(field_ptr, buf);
                            break;
                        case SOPC_Int32_Id:
                            status = SOPC_Int32_Write(field_ptr, buf);
                            break;
                        case SOPC_UInt32_Id:
                            status = SOPC_UInt32_Write(field_ptr, buf);
                            break;
                        case SOPC_Double_Id:
                            status = SOPC_Double_Write(field_ptr, buf);
                            break;
                        case SOPC_DateTime_Id:
                            status = SOPC_DateTime_Write(field_ptr, buf);
                            break;
                        case SOPC_NodeId_Id:
                            status = SOPC_NodeId_Write(field_ptr, buf);
                            break;
                        case SOPC_QualifiedName_Id:
                            status = SOPC_QualifiedName_Write(field_ptr, buf);
                            break;
                        default:
                            status = SOPC_STATUS_NOK;
                            assert(false);
                    }
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
                    switch(field_desc->Type.BuiltInId)
                    {
                        case SOPC_Boolean_Id:
                            allocation_size = sizeof (SOPC_Boolean);
                            read_fctn = &SOPC_Boolean_ReadAux;
                            init_fctn = &SOPC_Boolean_InitializeAux;
                            clear_fctn = &SOPC_Boolean_ClearAux;
                            break;
                        case SOPC_SByte_Id:
                            allocation_size = sizeof (int8_t);
                            read_fctn = &SOPC_SByte_ReadAux;
                            init_fctn = &SOPC_SByte_InitializeAux;
                            clear_fctn = &SOPC_SByte_ClearAux;
                            break;
                        case SOPC_Byte_Id:
                            allocation_size = sizeof (uint8_t);
                            read_fctn = &SOPC_Byte_ReadAux;
                            init_fctn = &SOPC_Byte_InitializeAux;
                            clear_fctn = &SOPC_Byte_ClearAux;
                            break;
                        case SOPC_Int16_Id:
                            allocation_size = sizeof (int16_t);
                            read_fctn = &SOPC_Int16_ReadAux;
                            init_fctn = &SOPC_Int16_InitializeAux;
                            clear_fctn = &SOPC_Int16_ClearAux;
                            break;
                        case SOPC_Int32_Id:
                            allocation_size = sizeof (int32_t);
                            read_fctn = &SOPC_Int32_ReadAux;
                            init_fctn = &SOPC_Int32_InitializeAux;
                            clear_fctn = &SOPC_Int32_ClearAux;
                            break;
                        case SOPC_UInt32_Id:
                            allocation_size = sizeof (uint32_t);
                            read_fctn = &SOPC_UInt32_ReadAux;
                            init_fctn = &SOPC_UInt32_InitializeAux;
                            clear_fctn = &SOPC_UInt32_ClearAux;
                            break;
                        case SOPC_Double_Id:
                            allocation_size = sizeof (double);
                            read_fctn = &SOPC_Double_ReadAux;
                            init_fctn = &SOPC_Double_InitializeAux;
                            clear_fctn = &SOPC_Double_ClearAux;
                            break;
                        case SOPC_DateTime_Id:
                            allocation_size = sizeof (SOPC_DateTime);
                            read_fctn = &SOPC_DateTime_ReadAux;
                            init_fctn = &SOPC_DateTime_InitializeAux;
                            clear_fctn = &SOPC_DateTime_ClearAux;
                            break;
                        case SOPC_NodeId_Id:
                            allocation_size = sizeof (SOPC_NodeId);
                            read_fctn = &SOPC_NodeId_ReadAux;
                            init_fctn = &SOPC_NodeId_InitializeAux;
                            clear_fctn = &SOPC_NodeId_ClearAux;
                            break;
                        case SOPC_QualifiedName_Id:
                            allocation_size = sizeof (SOPC_QualifiedName);
                            read_fctn = &SOPC_QualifiedName_ReadAux;
                            init_fctn = &SOPC_QualifiedName_InitializeAux;
                            clear_fctn = &SOPC_QualifiedName_ClearAux;
                            break;
                        default:
                            assert(false);
                    }
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
                    switch(field_desc->Type.BuiltInId)
                    {
                        case SOPC_Boolean_Id:
                            status = SOPC_Boolean_Read(field_ptr, buf);
                            break;
                        case SOPC_SByte_Id:
                            status = SOPC_SByte_Read(field_ptr, buf);
                            break;
                        case SOPC_Byte_Id:
                            status = SOPC_Byte_Read(field_ptr, buf);
                            break;
                        case SOPC_Int16_Id:
                            status = SOPC_Int16_Read(field_ptr, buf);
                            break;
                        case SOPC_Int32_Id:
                            status = SOPC_Int32_Read(field_ptr, buf);
                            break;
                        case SOPC_UInt32_Id:
                            status = SOPC_UInt32_Read(field_ptr, buf);
                            break;
                        case SOPC_Double_Id:
                            status = SOPC_Double_Read(field_ptr, buf);
                            break;
                        case SOPC_DateTime_Id:
                            status = SOPC_DateTime_Read(field_ptr, buf);
                            break;
                        case SOPC_NodeId_Id:
                            status = SOPC_NodeId_Read(field_ptr, buf);
                            break;
                        case SOPC_QualifiedName_Id:
                            status = SOPC_QualifiedName_Read(field_ptr, buf);
                            break;
                        default:
                            status = SOPC_STATUS_NOK;
                            assert(false);
                    }
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