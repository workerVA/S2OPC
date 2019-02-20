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

#include <string.h>

#include "sopc_builtintypes.h"
#include "sopc_helper_string.h"
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

void SOPC_Generic_Initialize(void* pValue, SOPC_EncodeableType* enc_type)
{
    // Initializing encodeable type
    void* field_ptr = ((char*) pValue);
    SOPC_EncodeableType** field_ec_type = (SOPC_EncodeableType**) field_ptr;
    *field_ec_type = enc_type;

    // Initializing fields
    for (uint32_t i = 0 ; i < enc_type->descriptor->nbElements ; i++)
    {
        // Getting the field
        field_ptr = ((char*) pValue) + enc_type->descriptor->Elements[i].Offset;

        if (enc_type->descriptor->Elements[i].IsBuiltIn)
        {
            switch(enc_type->descriptor->Elements[i].Id.BuiltInId)
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
                case SOPC_UInt16_Id:
                    break;
                case SOPC_Int32_Id:
                    break;
                case SOPC_UInt32_Id:
                    break;
                case SOPC_Int64_Id: 
                    break;
                case SOPC_UInt64_Id:
                    break;
                case SOPC_Float_Id: 
                    break;
                case SOPC_Double_Id:
                    SOPC_Double_Initialize(field_ptr);
                    break;
                case SOPC_String_Id:
                    break;
                case SOPC_DateTime_Id:
                    SOPC_DateTime_Initialize(field_ptr);
                    break;
                case SOPC_Guid_Id:
                    break;
                case SOPC_ByteString_Id:
                    break;
                case SOPC_XmlElement_Id:
                    break;
                case SOPC_NodeId_Id:
                    break;
                case SOPC_ExpandedNodeId_Id:
                    break;
                case SOPC_StatusCode_Id:
                    break;
                case SOPC_QualifiedName_Id:
                    break;
                case SOPC_LocalizedText_Id:
                    break;
                case SOPC_ExtensionObject_Id:
                    break;
                case SOPC_DataValue_Id:
                    break;
                case SOPC_Variant_Id:
                    break;
                case SOPC_DiagnosticInfo_Id:
                    break;
                default:
                    ;
            }
        }
        else
        {
            SOPC_Generic_Initialize(field_ptr, enc_type->descriptor->Elements[i].Id.NestedEncType);
        }
    }
}
