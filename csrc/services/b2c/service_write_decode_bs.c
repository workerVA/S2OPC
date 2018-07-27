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

/** \file
 *
 * Implements the getters for the write request.
 */

#include "service_write_decode_bs.h"
#include "b2c.h"

#include "address_space_impl.h" /* e_aid_* */
#include "sopc_types.h"

#include <assert.h>
#include <stdlib.h>

/* Globals */
static OpcUa_WriteRequest* request;

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void service_write_decode_bs__INITIALISATION(void)
{
    request = NULL;
}

/*--------------------
   OPERATIONS Clause
  --------------------*/

/*@ requires \valid(req);
  @ requires \valid(service_write_decode_bs__StatusCode_service);
  @ requires (0 < req->NoOfNodesToWrite && req->NoOfNodesToWrite <= constants__k_n_WriteResponse_max) ==>
  \valid(request);
  @ assigns request;
  @ assigns *service_write_decode_bs__StatusCode_service;
  @
  @ behavior e_sc_ok:
  @     assumes 0 < req->NoOfNodesToWrite && req->NoOfNodesToWrite <= constants__k_n_WriteResponse_max;
  @     ensures request == req;
  @     ensures *service_write_decode_bs__StatusCode_service == constants__e_sc_ok;
  @
  @ behavior e_sc_bad_nothing_to_do:
  @     assumes 0 >= req->NoOfNodesToWrite;
  @     ensures *service_write_decode_bs__StatusCode_service == constants__e_sc_bad_nothing_to_do;
  @
  @ behavior e_sc_bad_too_many_ops:
  @     assumes req->NoOfNodesToWrite > constants__k_n_WriteResponse_max;
  @     ensures *service_write_decode_bs__StatusCode_service == constants__e_sc_bad_too_many_ops;
  @
  @ disjoint behaviors;
  @ complete behaviors;
 */

static void s_decode_write_request(OpcUa_WriteRequest* req,
                                   constants__t_StatusCode_i* const service_write_decode_bs__StatusCode_service)
{
    if (req->NoOfNodesToWrite <= 0)
    {
        *service_write_decode_bs__StatusCode_service = constants__e_sc_bad_nothing_to_do;
    }
    else if (req->NoOfNodesToWrite > constants__k_n_WriteResponse_max)
    {
        *service_write_decode_bs__StatusCode_service = constants__e_sc_bad_too_many_ops;
    }
    else
    {
        /* TODO: req shall not be freed before request is null... */
        request = req;
        *service_write_decode_bs__StatusCode_service = constants__e_sc_ok;
    }
}

#ifndef __FRAMAC__
void service_write_decode_bs__decode_write_request(
    const constants__t_msg_i service_write_decode_bs__write_msg,
    constants__t_StatusCode_i* const service_write_decode_bs__StatusCode_service)
{
    assert(*(SOPC_EncodeableType**) service_write_decode_bs__write_msg == &OpcUa_WriteRequest_EncodeableType);

    OpcUa_WriteRequest* req = (OpcUa_WriteRequest*) service_write_decode_bs__write_msg;

    s_decode_write_request(req, service_write_decode_bs__StatusCode_service);
}
#endif //__FRAMAC__

/*@ requires \valid(request);
  @ assigns request;
  @ ensures request == \null;
 */

void service_write_decode_bs__free_write_request(void)
{
    request = NULL;
}

/*@ requires \valid(service_write_decode_bs__nb_req);
  @ requires \valid(request);
  @ assigns *service_write_decode_bs__nb_req;
  @ ensures not_NULL_request: (\null != request) ==> *service_write_decode_bs__nb_req == request->NoOfNodesToWrite;
  @ ensures is_NULL_request: (\null == request) ==> *service_write_decode_bs__nb_req == 0;
 */

void service_write_decode_bs__get_nb_WriteValue(t_entier4* const service_write_decode_bs__nb_req)
{
    /* TODO: does B prevent this operation from being called before decode ? */
    if (NULL != request)
        *service_write_decode_bs__nb_req = request->NoOfNodesToWrite;
    else
        *service_write_decode_bs__nb_req = 0;
}

/**
 * Note: When using request as a OpcUa_WriteRequest,
 * \p nid and \p value are borrowed from request,
 * you should not free them.
 */

/*@ requires \valid(service_write_decode_bs__isvalid);
  @ requires \valid(service_write_decode_bs__status);
  @ requires \valid(service_write_decode_bs__nid);
  @ requires \valid(service_write_decode_bs__aid);
  @ requires \valid(service_write_decode_bs__value);
  @ requires \separated(service_write_decode_bs__status, service_write_decode_bs__nid,
  service_write_decode_bs__aid, service_write_decode_bs__value, service_write_decode_bs__isvalid,
  request, request->NodesToWrite+(service_write_decode_bs__wvi - 1));
  @ requires 1 <= service_write_decode_bs__wvi <= request->NoOfNodesToWrite;
  @ requires \valid(request);
  @ requires \valid(request->NodesToWrite+(service_write_decode_bs__wvi - 1));
  @ assigns *service_write_decode_bs__isvalid;
  @ assigns *service_write_decode_bs__status;
  @ assigns *service_write_decode_bs__aid;
  @ assigns *service_write_decode_bs__nid;
  @ assigns *service_write_decode_bs__value;
  @
  @ behavior correct_attributeId :
  @     assumes (request->NodesToWrite[service_write_decode_bs__wvi - 1]).AttributeId \in {e_aid_NodeId,
  e_aid_NodeClass, e_aid_Value};
  @     ensures *service_write_decode_bs__isvalid == true;
  @     ensures *service_write_decode_bs__status == constants__c_StatusCode_indet;
  @     ensures *service_write_decode_bs__nid == &(request->NodesToWrite[service_write_decode_bs__wvi - 1]).NodeId;
  @     ensures *service_write_decode_bs__value == &(request->NodesToWrite[service_write_decode_bs__wvi -
  1]).Value.Value;
  @     ensures (request->NodesToWrite[service_write_decode_bs__wvi - 1]).AttributeId == e_aid_NodeId
  ==> *service_write_decode_bs__aid == constants__e_aid_NodeId;
  @     ensures (request->NodesToWrite[service_write_decode_bs__wvi - 1]).AttributeId == e_aid_NodeClass
  ==> *service_write_decode_bs__aid == constants__e_aid_NodeClass;
  @     ensures (request->NodesToWrite[service_write_decode_bs__wvi - 1]).AttributeId == e_aid_Value
  ==> *service_write_decode_bs__aid == constants__e_aid_Value;
  @
  @ behavior incorrect_attributeId :
  @     assumes !((request->NodesToWrite[service_write_decode_bs__wvi - 1]).AttributeId \in {e_aid_NodeId,
  e_aid_NodeClass, e_aid_Value});
  @     ensures *service_write_decode_bs__isvalid == false;
  @     ensures *service_write_decode_bs__status == constants__e_sc_bad_attribute_id_invalid;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */
void service_write_decode_bs__getall_WriteValue(const constants__t_WriteValue_i service_write_decode_bs__wvi,
                                                t_bool* const service_write_decode_bs__isvalid,
                                                constants__t_StatusCode_i* const service_write_decode_bs__status,
                                                constants__t_NodeId_i* const service_write_decode_bs__nid,
                                                constants__t_AttributeId_i* const service_write_decode_bs__aid,
                                                constants__t_Variant_i* const service_write_decode_bs__value)
{
    *service_write_decode_bs__nid = constants__c_NodeId_indet;
    *service_write_decode_bs__value = constants__c_Variant_indet;

    OpcUa_WriteValue* wv = &request->NodesToWrite[service_write_decode_bs__wvi - 1];
    *service_write_decode_bs__isvalid = true;
    switch (wv->AttributeId)
    {
    case e_aid_NodeId:
        *service_write_decode_bs__aid = constants__e_aid_NodeId;
        break;
    case e_aid_NodeClass:
        *service_write_decode_bs__aid = constants__e_aid_NodeClass;
        break;
    case e_aid_Value:
        *service_write_decode_bs__aid = constants__e_aid_Value;
        break;
    default:
        *service_write_decode_bs__isvalid = false;
        *service_write_decode_bs__status = constants__e_sc_bad_attribute_id_invalid;
        break;
    }
    if (*service_write_decode_bs__isvalid == true)
    {
        if (wv->IndexRange.Length > 0)
        {
            *service_write_decode_bs__isvalid = false;
            *service_write_decode_bs__status = constants__e_sc_bad_index_range_invalid;
        }
    }
    if (*service_write_decode_bs__isvalid == true)
    {
        *service_write_decode_bs__nid = &wv->NodeId;
        *service_write_decode_bs__value = &wv->Value.Value;
    }
}

/*@ ghost int has_mem; */

/*@ requires \true;
  @ assigns \nothing;
  @ behavior allocated:
  @     assumes has_mem;
  @     ensures \valid(\result + (0 .. nb-1));
  @
  @ behavior not_allocated:
  @     assumes !has_mem;
  @     ensures \result == \null;
  @
  @ disjoint behaviors;
  @ complete behaviors;

*/

static OpcUa_WriteValue* writevalue_malloc(size_t size, size_t nb);

#ifndef __FRAMAC__
static OpcUa_WriteValue* writevalue_malloc(size_t size, size_t nb)
{
    return (OpcUa_WriteValue*) malloc(size * nb);
}
#endif // __FRAMAC__

<<<<<<< cc06b6239f22880b0de6c7ddab891fd2caba1925
void service_write_decode_bs__getall_WriteValuePointer(
    const constants__t_WriteValue_i service_write_decode_bs__wvi,
    constants__t_WriteValuePointer_i* const service_write_decode_bs__wvPointer)
{
    *service_write_decode_bs__wvPointer = &request->NodesToWrite[service_write_decode_bs__wvi - 1];
=======
/*@ predicate is_clean_NodeId(SOPC_NodeId a_NodeId) =
  @ a_NodeId.IdentifierType == 0 &&
  @ a_NodeId.Namespace == 0 &&
  @ a_NodeId.Data.Numeric == 0;
  @
  @ predicate is_clean_AttribueId(uint32_t a_AttributeId) =
  @ a_AttributeId == 0;
  @
  @ predicate is_clean_IndexRange(SOPC_String a_IndexRange) =
  @ a_IndexRange.Length == -1 &&
  @ a_IndexRange.DoNotClear == false &&
  @ a_IndexRange.Data == \null;
  @
  @ predicate is_clean_DataValue(SOPC_DataValue a_Value) =
  @ a_Value.Value.DoNotClear == 0 &&
  @ a_Value.Value.BuiltInTypeId == 0 &&
  @ a_Value.Value.ArrayType == 0x0 &&
  @ a_Value.Value.Value.Boolean == 0 &&
  @ a_Value.Status == 0 &&
  @ a_Value.SourceTimestamp == 0 &&
  @ a_Value.ServerTimestamp == 0 &&
  @ a_Value.SourcePicoSeconds == 0 &&
  @ a_Value.ServerPicoSeconds == 0;
  @
  @ predicate is_clean_wv(OpcUa_WriteValue a_wv) =
  @ (a_wv.encodeableType) == &OpcUa_WriteValue_EncodeableType &&
  @ is_clean_NodeId(a_wv.NodeId) &&
  @ is_clean_AttribueId(a_wv.AttributeId) &&
  @ is_clean_IndexRange(a_wv.IndexRange) &&
  @ is_clean_DataValue(a_wv.Value);
 */

/*@ requires \valid(write_value);
  @ assigns *write_value;
  @ ensures is_clean_wv(*write_value);
 */

static void writevalue_initialize(OpcUa_WriteValue* write_value);

#ifndef __FRAMAC__
static void writevalue_initialize(OpcUa_WriteValue* write_value)
{
    OpcUa_WriteValue_Initialize(write_value);
}
#endif

/*@ requires service_write_decode_bs__wvi >= 1;
  @ requires \valid(request);
  @ requires \valid(request->NodesToWrite + (service_write_decode_bs__wvi - 1));
  @ requires \valid(service_write_decode_bs__wvPointer);
  @ requires \separated(service_write_decode_bs__wvPointer, *service_write_decode_bs__wvPointer,
  request->NodesToWrite+(service_write_decode_bs__wvi - 1));
  @ assigns *service_write_decode_bs__wvPointer;
  @ assigns \at(**service_write_decode_bs__wvPointer, Post);
  @ assigns request->NodesToWrite[service_write_decode_bs__wvi - 1];
  @
  @ ensures has_mem ==> \at(**service_write_decode_bs__wvPointer, Post) ==
  \at(request->NodesToWrite[service_write_decode_bs__wvi - 1], Pre);
  @ ensures !has_mem ==> \null == *service_write_decode_bs__wvPointer;
  @ ensures is_clean_wv(\at(request->NodesToWrite[service_write_decode_bs__wvi - 1], Post));
 */

void service_write_decode_bs__getAndClean_WriteValuePointer(
    const constants__t_WriteValue_i service_write_decode_bs__wvi,
    constants__t_WriteValuePointer_i* const service_write_decode_bs__wvPointer)
{
    OpcUa_WriteValue tmp = request->NodesToWrite[service_write_decode_bs__wvi - 1];

    *service_write_decode_bs__wvPointer = writevalue_malloc(sizeof(OpcUa_WriteValue), 1);
    writevalue_initialize(&request->NodesToWrite[service_write_decode_bs__wvi - 1]);
    if (NULL != *service_write_decode_bs__wvPointer)
    {
        **service_write_decode_bs__wvPointer = tmp;
        /* Re-Init the WriteValue to avoid deallocation of its content now copied in new WriteValue */
    }
    //*service_write_decode_bs__wvPointer = wv;
>>>>>>> Ticket #000: Proved msg_read_request_bs.c
}
