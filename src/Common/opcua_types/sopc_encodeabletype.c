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

#include <assert.h>
#include <string.h>

#include "sopc_builtintypes.h"
#include "sopc_encoder.h"
#include "sopc_helper_string.h"
#include "sopc_logger.h"
#include "sopc_macros.h"
#include "sopc_types.h"

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

static size_t getAllocationSize(const SOPC_EncodeableType_FieldDescriptor* desc)
{
    if (desc->isBuiltIn)
    {
        return SOPC_BuiltInType_HandlingTable[desc->typeIndex].size;
    }
    return SOPC_KnownEncodeableTypes[desc->typeIndex]->AllocationSize;
}

static SOPC_EncodeableObject_PfnInitialize* getPfnInitialize(const SOPC_EncodeableType_FieldDescriptor* desc)
{
    if (desc->isBuiltIn)
    {
        return SOPC_BuiltInType_HandlingTable[desc->typeIndex].initialize;
    }
    return SOPC_KnownEncodeableTypes[desc->typeIndex]->Initialize;
}

static SOPC_EncodeableObject_PfnClear* getPfnClear(const SOPC_EncodeableType_FieldDescriptor* desc)
{
    if (desc->isBuiltIn)
    {
        return SOPC_BuiltInType_HandlingTable[desc->typeIndex].clear;
    }
    return SOPC_KnownEncodeableTypes[desc->typeIndex]->Clear;
}

static SOPC_EncodeableObject_PfnEncode* getPfnEncode(const SOPC_EncodeableType_FieldDescriptor* desc)
{
    if (desc->isBuiltIn)
    {
        return SOPC_BuiltInType_EncodingTable[desc->typeIndex].encode;
    }
    return SOPC_KnownEncodeableTypes[desc->typeIndex]->Encode;
}

static SOPC_EncodeableObject_PfnDecode* getPfnDecode(const SOPC_EncodeableType_FieldDescriptor* desc)
{
    if (desc->isBuiltIn)
    {
        return SOPC_BuiltInType_EncodingTable[desc->typeIndex].decode;
    }
    return SOPC_KnownEncodeableTypes[desc->typeIndex]->Decode;
}

static void** retrieveArrayAddressPtr(void* pValue, const SOPC_EncodeableType_FieldDescriptor* arrayDesc)
{
    /* Avoid "warning: cast increases required alignment of target type [-Wcast-align]"
     * There is no issue in this case since arrayDesc->offset has been computed using 'offsetof' operator and
     * actually contains a void* address (address of the allocated array).
     * Therefore casting this address into a (void**) is valid and cannot lead to lose information on the
     * address due to alignment normalization (e.g.: when casting a char* to a int*, char* might not be aligned on
     * multiple of 4 bytes and then its address can be normalized to comply to this alignment after the cast
     * operation | see EXP36-C SEI CERT rule).*/
    SOPC_GCC_DIAGNOSTIC_PUSH
    SOPC_GCC_DIAGNOSTIC_IGNORE_CAST_ALIGN
    return (void**) ((char*) pValue + arrayDesc->offset);
    SOPC_GCC_DIAGNOSTIC_RESTORE
}

static const void* const* retrieveConstArrayAddressPtr(const void* pValue,
                                                       const SOPC_EncodeableType_FieldDescriptor* arrayDesc)
{
    /* See retrieveArrayAddressPtr comment */
    SOPC_GCC_DIAGNOSTIC_PUSH
    SOPC_GCC_DIAGNOSTIC_IGNORE_CAST_ALIGN
    return (const void* const*) ((const char*) pValue + arrayDesc->offset);
    SOPC_GCC_DIAGNOSTIC_RESTORE
}

void SOPC_EncodeableObject_Initialize(SOPC_EncodeableType* type, void* pValue)
{
    assert(type != NULL);
    assert(pValue != NULL);

    // The first field of all non-builtin OPC UA type instances is its encodeable type
    *((SOPC_EncodeableType**) pValue) = type;

    for (int32_t i = 0; i < type->NoOfFields; ++i)
    {
        const SOPC_EncodeableType_FieldDescriptor* desc = &type->Fields[i];
        void* pField = (char*) pValue + desc->offset;
        SOPC_EncodeableObject_PfnInitialize* initFunction = NULL;

        if (desc->isArrayLength)
        {
            int32_t* pLength = NULL;
            const SOPC_EncodeableType_FieldDescriptor* arrayDesc = NULL;
            void** pArray = NULL;
            size_t size = 0;

            assert(desc->isBuiltIn);
            assert(desc->typeIndex == (uint32_t) SOPC_Int32_Id);
            pLength = pField;

            ++i;
            assert(i < type->NoOfFields);
            arrayDesc = &type->Fields[i];
            pArray = retrieveArrayAddressPtr(pValue, arrayDesc);
            size = getAllocationSize(arrayDesc);
            initFunction = getPfnInitialize(arrayDesc);

            SOPC_Initialize_Array(pLength, pArray, size, initFunction);
        }
        else
        {
            initFunction = getPfnInitialize(desc);
            initFunction(pField);
        }
    }
}

void SOPC_EncodeableObject_Clear(SOPC_EncodeableType* type, void* pValue)
{
    assert(type != NULL);
    if (NULL == pValue)
    {
        return;
    }

    for (int32_t i = 0; i < type->NoOfFields; ++i)
    {
        const SOPC_EncodeableType_FieldDescriptor* desc = &type->Fields[i];
        void* pField = (char*) pValue + desc->offset;
        SOPC_EncodeableObject_PfnClear* clearFunction = NULL;

        if (desc->isArrayLength)
        {
            int32_t* pLength = NULL;
            const SOPC_EncodeableType_FieldDescriptor* arrayDesc = NULL;
            void** pArray = NULL;
            size_t size = 0;

            assert(desc->isBuiltIn);
            assert(desc->typeIndex == (uint32_t) SOPC_Int32_Id);
            pLength = pField;

            ++i;
            assert(i < type->NoOfFields);
            arrayDesc = &type->Fields[i];
            pArray = retrieveArrayAddressPtr(pValue, arrayDesc);
            size = getAllocationSize(arrayDesc);
            clearFunction = getPfnClear(arrayDesc);

            SOPC_Clear_Array(pLength, pArray, size, clearFunction);
        }
        else
        {
            clearFunction = getPfnClear(desc);
            clearFunction(pField);
        }
    }
}

SOPC_ReturnStatus SOPC_EncodeableObject_Encode(const SOPC_EncodeableType* type, const void* pValue, SOPC_Buffer* buf)
{
    SOPC_ReturnStatus status = SOPC_STATUS_INVALID_PARAMETERS;

    if (type != NULL && pValue != NULL && buf != NULL && *((SOPC_EncodeableType* const*) pValue) == type)
    {
        status = SOPC_STATUS_OK;
    }
    else if (type != NULL && pValue != NULL && *((SOPC_EncodeableType* const*) pValue) != type)
    {
        SOPC_Logger_TraceWarning(
            "Problem encoding type %s value. Value 'encodeableType' field incorrectly initialized.", type->TypeName);
    }

    for (int32_t i = 0; SOPC_STATUS_OK == status && i < type->NoOfFields; ++i)
    {
        const SOPC_EncodeableType_FieldDescriptor* desc = &type->Fields[i];
        const void* pField = (const char*) pValue + desc->offset;

        if (!desc->isToEncode)
        {
            // Skip this field
        }
        else if (desc->isArrayLength)
        {
            const int32_t* pLength = NULL;
            const SOPC_EncodeableType_FieldDescriptor* arrayDesc = NULL;
            const void* const* pArray = NULL;
            size_t size = 0;
            SOPC_EncodeableObject_PfnEncode* encodeFunction = NULL;

            assert(desc->isBuiltIn);
            assert(desc->typeIndex == (uint32_t) SOPC_Int32_Id);
            pLength = pField;

            ++i;
            assert(i < type->NoOfFields);
            arrayDesc = &type->Fields[i];
            pArray = retrieveConstArrayAddressPtr(pValue, arrayDesc);
            size = getAllocationSize(arrayDesc);
            encodeFunction = getPfnEncode(arrayDesc);

            status = SOPC_Write_Array(buf, pLength, pArray, size, encodeFunction);
        }
        else
        {
            SOPC_EncodeableObject_PfnEncode* encodeFunction = getPfnEncode(desc);
            status = encodeFunction(pField, buf);
        }
    }

    return status;
}

SOPC_ReturnStatus SOPC_EncodeableObject_Decode(SOPC_EncodeableType* type, void* pValue, SOPC_Buffer* buf)
{
    SOPC_ReturnStatus status = SOPC_STATUS_INVALID_PARAMETERS;

    if (type != NULL && pValue != NULL && buf != NULL)
    {
        status = SOPC_STATUS_OK;
    }

    if (SOPC_STATUS_OK == status)
    {
        SOPC_EncodeableObject_Initialize(type, pValue);
    }

    for (int32_t i = 0; SOPC_STATUS_OK == status && i < type->NoOfFields; ++i)
    {
        const SOPC_EncodeableType_FieldDescriptor* desc = &type->Fields[i];
        void* pField = (char*) pValue + desc->offset;
        SOPC_EncodeableObject_PfnDecode* decodeFunction = NULL;

        if (!desc->isToEncode)
        {
            // Skip this field
        }
        else if (desc->isArrayLength)
        {
            int32_t* pLength = NULL;
            const SOPC_EncodeableType_FieldDescriptor* arrayDesc = NULL;
            void** pArray = NULL;
            size_t size = 0;
            SOPC_EncodeableObject_PfnInitialize* initFunction = NULL;
            SOPC_EncodeableObject_PfnClear* clearFunction = NULL;

            assert(desc->isBuiltIn);
            assert(desc->typeIndex == (uint32_t) SOPC_Int32_Id);
            pLength = pField;

            ++i;
            assert(i < type->NoOfFields);
            arrayDesc = &type->Fields[i];
            pArray = retrieveArrayAddressPtr(pValue, arrayDesc);
            size = getAllocationSize(arrayDesc);
            decodeFunction = getPfnDecode(arrayDesc);
            initFunction = getPfnInitialize(arrayDesc);
            clearFunction = getPfnClear(arrayDesc);

            status = SOPC_Read_Array(buf, pLength, pArray, size, decodeFunction, initFunction, clearFunction);
        }
        else
        {
            decodeFunction = getPfnDecode(desc);
            status = decodeFunction(pField, buf);
        }
    }

    if (status != SOPC_STATUS_OK && type != NULL && pValue != NULL)
    {
        SOPC_EncodeableObject_Clear(type, pValue);
    }

    return status;
}