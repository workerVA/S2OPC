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
  @ assigns *service_write_decode_bs__StatusCode_service;
  @	assigns request;
  @
  @ behavior e_sc_ok:
  @		assumes 0 < NoOfNodesToWrite && NoOfNodesToWrite <= constants__k_n_WriteResponse_max;
  @ 	ensures request == req;
  @ 	ensures *service_write_decode_bs__StatusCode_service == constants__e_sc_ok;
  @
  @ behavior e_sc_bad_nothing_to_do:
  @		assumes 0 >= NoOfNodesToWrite;
  @ 	ensures *service_write_decode_bs__StatusCode_service == constants__e_sc_bad_nothing_to_do;
  @ 	ensures request == \old(request);
  @
  @ behavior e_sc_bad_too_many_ops:
  @ 	assumes NoOfNodesToWrite > constants__k_n_WriteResponse_max;
  @ 	ensures *service_write_decode_bs__StatusCode_service == constants__e_sc_bad_too_many_ops;
  @ 	ensures request == \old(request);
  @
  @ disjoint behaviors;
  @ complete behaviors;
 */

static void s_decode_write_request(OpcUa_WriteRequest* req,
                                   int32_t NoOfNodesToWrite,
                                   constants__t_StatusCode_i* const service_write_decode_bs__StatusCode_service)
{
    *service_write_decode_bs__StatusCode_service = constants__e_sc_bad_unexpected_error;

    if (0 < NoOfNodesToWrite && NoOfNodesToWrite <= constants__k_n_WriteResponse_max)
    {
        /* TODO: req shall not be freed before request is null... */
        request = req;
        *service_write_decode_bs__StatusCode_service = constants__e_sc_ok;
    }
    else
    {
        if (NoOfNodesToWrite <= 0)
        {
            *service_write_decode_bs__StatusCode_service = constants__e_sc_bad_nothing_to_do;
        }
        else if (NoOfNodesToWrite > constants__k_n_WriteResponse_max)
        {
            *service_write_decode_bs__StatusCode_service = constants__e_sc_bad_too_many_ops;
        }
    }
}

/*@ requires \valid(service_write_decode_bs__StatusCode_service);
  @ requires \valid((OpcUa_WriteRequest*) service_write_decode_bs__write_msg);
  @ assigns \nothing;
 */

void service_write_decode_bs__decode_write_request(
    const constants__t_msg_i service_write_decode_bs__write_msg,
    constants__t_StatusCode_i* const service_write_decode_bs__StatusCode_service)
{
    OpcUa_WriteRequest* req = (OpcUa_WriteRequest*) service_write_decode_bs__write_msg;

    s_decode_write_request(req, req->NoOfNodesToWrite, service_write_decode_bs__StatusCode_service);
}

/*@ requires \valid(service_write_decode_bs__StatusCode_service);
  @ requires \valid(service_write_decode_bs__write_msg);
  @ assigns \nothing;
 */

void service_write_decode_bs__decode_write_request2(
    const OpcUa_WriteRequest* service_write_decode_bs__write_msg,
    constants__t_StatusCode_i* const service_write_decode_bs__StatusCode_service)
{
    OpcUa_WriteRequest* req = service_write_decode_bs__write_msg;

    s_decode_write_request(req, req->NoOfNodesToWrite, service_write_decode_bs__StatusCode_service);
}

/*@ assigns request;
  @ ensures request == \null;
 */

void service_write_decode_bs__free_write_request(void)
{
    request = NULL;
}

/*@ requires \valid(service_write_decode_bs__nb_req);
  @ requires \valid(request);
  @ assigns *service_write_decode_bs__nb_req;
  @ ensures A: (NULL != request) ==> *service_write_decode_bs__nb_req == request->NoOfNodesToWrite && request;
  @ ensures B: (NULL == request) ==> *service_write_decode_bs__nb_req == 0;
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

void service_write_decode_bs__getall_WriteValuePointer(
    const constants__t_WriteValue_i service_write_decode_bs__wvi,
    constants__t_WriteValuePointer_i* const service_write_decode_bs__wvPointer)
{
    *service_write_decode_bs__wvPointer = &request->NodesToWrite[service_write_decode_bs__wvi - 1];
}
