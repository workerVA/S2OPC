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
 * Implements the base machine that reads a ReadRequest.
 */

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

#include "msg_read_request_bs.h"
#include "util_b2c.h"

#include "address_space_impl.h"
#include "sopc_logger.h"
#include "sopc_types.h"

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void msg_read_request_bs__INITIALISATION(void) {}

/*--------------------
   OPERATIONS Clause
  --------------------*/
// Number of valid ReadValue in the Read request
//@ ghost int nbNodesToRead;

static bool bWarned = false;

#ifdef __FRAMAC__
//@ assigns \nothing;
void SOPC_Logger_TraceWarning(const char* format, ...);
#endif // __FRAMAC__

/*@ predicate is_correct_AttributeId(uint32_t caid, constants__t_AttributeId_i baid) =
  @ (caid == e_aid_NodeId && baid == constants__e_aid_NodeId) ||
  @ (caid == e_aid_NodeClass && baid == constants__e_aid_NodeClass) ||
  @ (caid == e_aid_BrowseName && baid == constants__e_aid_BrowseName) ||
  @ (caid == e_aid_DisplayName && baid == constants__e_aid_DisplayName) ||
  @ (caid == e_aid_Value && baid == constants__e_aid_Value) ||
  @ (caid == e_aid_AccessLevel && baid == constants__e_aid_AccessLevel) ||
  @ (!(caid \in {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value, e_aid_AccessLevel})
  && baid == constants__c_AttributeId_indet);
 */

/*@ requires \valid(msg_read_req);
  @ requires \valid(msg_read_request_bs__sc);
  @ requires \valid(msg_read_request_bs__aid);
  @ requires msg_read_request_bs__rvi >= 0;
  @ requires nbNodesToRead >= msg_read_request_bs__rvi;
  @ requires constants__c_ReadValue_indet != msg_read_request_bs__rvi;
  @ requires \valid(msg_read_req->NodesToRead+(msg_read_request_bs__rvi - 1));
  @ requires \separated(msg_read_request_bs__aid, msg_read_request_bs__sc, msg_read_req,
  msg_read_req->NodesToRead, msg_read_req->NodesToRead+(msg_read_request_bs__rvi - 1));
  @ assigns *msg_read_request_bs__aid;
  @ assigns *msg_read_request_bs__sc;
  @ assigns bWarned;
  @
  @ behavior invalid_id:
  @     assumes !(msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId \in
  {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value, e_aid_AccessLevel});
  @     ensures *msg_read_request_bs__sc == constants__e_sc_bad_attribute_id_invalid;
  @     ensures *msg_read_request_bs__aid == constants__c_AttributeId_indet;
  @     ensures is_correct_AttributeId(msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId,
                                       *msg_read_request_bs__aid);
  @     ensures !\old(bWarned) ==> bWarned;
  @
  @ behavior has_index_range:
  @     assumes msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId \in
  {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value, e_aid_AccessLevel};
  @     assumes msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].IndexRange.Length > 0;
  @     ensures *msg_read_request_bs__sc == constants__e_sc_bad_index_range_invalid;
  @     ensures is_correct_AttributeId(msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId,
                                       *msg_read_request_bs__aid);
  @
  @ behavior ok:
  @     assumes msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId \in
  {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value, e_aid_AccessLevel};
  @     assumes msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].IndexRange.Length <= 0;
  @     ensures *msg_read_request_bs__sc == constants__e_sc_ok;
  @     ensures is_correct_AttributeId(msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId,
                                       *msg_read_request_bs__aid);
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */

static void s_getall_req_ReadValue_AttributeId(OpcUa_ReadRequest* msg_read_req,
                                               const constants__t_ReadValue_i msg_read_request_bs__rvi,
                                               constants__t_StatusCode_i* const msg_read_request_bs__sc,
                                               constants__t_AttributeId_i* const msg_read_request_bs__aid)
{
    *msg_read_request_bs__sc = constants__e_sc_ok;

    *msg_read_request_bs__aid = constants__c_AttributeId_indet;
    bool isvalid = util_AttributeId__C_to_B(msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId,
                                            msg_read_request_bs__aid);

    if (!isvalid)
    {
        *msg_read_request_bs__sc = constants__e_sc_bad_attribute_id_invalid;
        if (!bWarned)
        {
            SOPC_Logger_TraceWarning("msg_read_request_bs__getall_req_ReadValue_AttributeId: unsupported attribute id");
            bWarned = true;
        }
    }

    if (isvalid && msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].IndexRange.Length > 0)
    {
        isvalid = false;
        *msg_read_request_bs__sc = constants__e_sc_bad_index_range_invalid;
    }
}

#ifndef __FRAMAC__
void msg_read_request_bs__getall_req_ReadValue_AttributeId(const constants__t_msg_i msg_read_request_bs__msg,
                                                           const constants__t_ReadValue_i msg_read_request_bs__rvi,
                                                           constants__t_StatusCode_i* const msg_read_request_bs__sc,
                                                           constants__t_AttributeId_i* const msg_read_request_bs__aid)
{
    /* TODO: is message type checked at this point? */
    /* Added same assert as in service_write_decode_bs.c. Is it correct here ?*/
    assert(*(SOPC_EncodeableType**) msg_read_request_bs__msg == &OpcUa_ReadRequest_EncodeableType);

    OpcUa_ReadRequest* msg_read_req = (OpcUa_ReadRequest*) msg_read_request_bs__msg;

    s_getall_req_ReadValue_AttributeId(msg_read_req, msg_read_request_bs__rvi, msg_read_request_bs__sc,
                                       msg_read_request_bs__aid);
}
#endif // __FRAMAC__

/*@ requires \valid(msg_read_req);
  @ requires \valid(msg_read_request_bs__nid);
  @ requires 0 <= msg_read_request_bs__rvi <= nbNodesToRead;
  @ requires constants__c_ReadValue_indet != msg_read_request_bs__rvi;
  @ requires \valid(msg_read_req->NodesToRead+(msg_read_request_bs__rvi - 1));
  @ requires \separated(msg_read_req, msg_read_request_bs__nid);
  @ assigns *msg_read_request_bs__nid;
  @ ensures *msg_read_request_bs__nid == &msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].NodeId;
 */

static void s_getall_req_ReadValue_NodeId(OpcUa_ReadRequest* msg_read_req,
                                          const constants__t_ReadValue_i msg_read_request_bs__rvi,
                                          constants__t_NodeId_i* const msg_read_request_bs__nid)
{
    *msg_read_request_bs__nid = &msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].NodeId;
}

#ifndef __FRAMAC__
void msg_read_request_bs__getall_req_ReadValue_NodeId(const constants__t_msg_i msg_read_request_bs__msg,
                                                      const constants__t_ReadValue_i msg_read_request_bs__rvi,
                                                      constants__t_NodeId_i* const msg_read_request_bs__nid)
{
    OpcUa_ReadRequest* msg_read_req = (OpcUa_ReadRequest*) msg_read_request_bs__msg;

    s_getall_req_ReadValue_NodeId(msg_read_req, msg_read_request_bs__rvi, msg_read_request_bs__nid);
}
#endif // __FRAMAC__

/*@ requires \valid(msg_read_req);
  @ requires \valid(msg_read_request_bs__p_tsToReturn);
  @ requires \separated(msg_read_req, msg_read_request_bs__p_tsToReturn);
  @ assigns *msg_read_request_bs__p_tsToReturn;
  */

static void s_read_req_TimestampsToReturn(OpcUa_ReadRequest* msg_read_req,
                                          constants__t_TimestampsToReturn_i* const msg_read_request_bs__p_tsToReturn)
{
    *msg_read_request_bs__p_tsToReturn = util_TimestampsToReturn__C_to_B(msg_read_req->TimestampsToReturn);
}

#ifndef __FRAMAC__
void msg_read_request_bs__read_req_TimestampsToReturn(
    const constants__t_msg_i msg_read_request_bs__p_msg,
    constants__t_TimestampsToReturn_i* const msg_read_request_bs__p_tsToReturn)
{
    OpcUa_ReadRequest* msg_read_req = (OpcUa_ReadRequest*) msg_read_request_bs__p_msg;
    s_read_req_TimestampsToReturn(msg_read_req, msg_read_request_bs__p_tsToReturn);
}
#endif // __FRAMAC__

/*@ requires \valid(msg_read_req);
  @ requires \valid(msg_read_request_bs__p_maxAge_valid);
  @ assigns *msg_read_request_bs__p_maxAge_valid;
  @ ensures *msg_read_request_bs__p_maxAge_valid <==> msg_read_req->MaxAge >= 0;
 */

static void s_read_req_MaxAge(OpcUa_ReadRequest* msg_read_req, t_bool* const msg_read_request_bs__p_maxAge_valid)
{
    *msg_read_request_bs__p_maxAge_valid = msg_read_req->MaxAge >= 0;
}

#ifndef __FRAMAC__
void msg_read_request_bs__read_req_MaxAge(const constants__t_msg_i msg_read_request_bs__p_msg,
                                          t_bool* const msg_read_request_bs__p_maxAge_valid)
{
    OpcUa_ReadRequest* msg_read_req = (OpcUa_ReadRequest*) msg_read_request_bs__p_msg;

    s_read_req_MaxAge(msg_read_req, msg_read_request_bs__p_maxAge_valid);
}
#endif // __FRAMAC__

/*@ requires \valid(msg_read_req);
  @ requires \valid(msg_read_request_bs__nb);
  @ assigns *msg_read_request_bs__nb;
  @ assigns nbNodesToRead;
  @ ensures *msg_read_request_bs__nb == msg_read_req->NoOfNodesToRead;
  @ ensures nbNodesToRead == msg_read_req->NoOfNodesToRead;
 */

static void s_read_req_nb_ReadValue(OpcUa_ReadRequest* msg_read_req, t_entier4* const msg_read_request_bs__nb)
{
    *msg_read_request_bs__nb = msg_read_req->NoOfNodesToRead;
    //@ ghost nbNodesToRead = msg_read_req->NoOfNodesToRead;
}

#ifndef __FRAMAC__
void msg_read_request_bs__read_req_nb_ReadValue(const constants__t_msg_i msg_read_request_bs__msg,
                                                t_entier4* const msg_read_request_bs__nb)
{
    OpcUa_ReadRequest* msg_read_req = (OpcUa_ReadRequest*) msg_read_request_bs__msg;

    s_read_req_nb_ReadValue(msg_read_req, msg_read_request_bs__nb);
}
#endif // __FRAMAC__
