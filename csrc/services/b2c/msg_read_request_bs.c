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

static bool bWarned = false;

/*@ requires pbaid == \null || \valid(pbaid);
  @ assigns *pbaid;
  @
  @ behavior valid_ptr:
  @ 	assumes pbaid != \null;
  @ 	ensures caid == e_aid_NodeId ==> *pbaid == constants__e_aid_NodeId;
  @ 	ensures caid == e_aid_NodeClass ==> *pbaid == constants__e_aid_NodeClass;
  @ 	ensures caid == e_aid_BrowseName ==> *pbaid == constants__e_aid_BrowseName;
  @ 	ensures caid == e_aid_DisplayName ==> *pbaid == constants__e_aid_DisplayName;
  @ 	ensures caid == e_aid_Value ==> *pbaid == constants__e_aid_Value;
  @ 	ensures caid == e_aid_AccessLevel ==> *pbaid == constants__e_aid_AccessLevel;
  @ 	ensures \result <==> caid \in {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value,
  e_aid_AccessLevel};
  @ 	ensures !(caid \in {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value,
  e_aid_AccessLevel}) ==> *pbaid == \at(*pbaid, Pre);
  @
  @ behavior invalid_ptr:
  @ 	assumes pbaid == \null;
  @ 	ensures \result == \false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */

static bool s_AttributeId(uint32_t caid, constants__t_AttributeId_i* pbaid);

#ifndef __FRAMAC__
static bool s_AttributeId(uint32_t caid, constants__t_AttributeId_i* pbaid)
{
    return util_AttributeId__C_to_B(caid, pbaid);
}
#endif // __FRAMAC__

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
  @ requires \valid(msg_read_request_bs__isvalid);
  @ requires \valid(msg_read_request_bs__aid);
  @ requires msg_read_request_bs__rvi >= 1;
  @ requires \valid(msg_read_req->NodesToRead+(msg_read_request_bs__rvi - 1));
  @ requires \separated(msg_read_request_bs__aid, msg_read_request_bs__isvalid, msg_read_req,
  msg_read_req->NodesToRead, msg_read_req->NodesToRead+(msg_read_request_bs__rvi - 1));
  @ assigns *msg_read_request_bs__aid;
  @ assigns *msg_read_request_bs__isvalid;
  @ assigns bWarned;
  @
  @ ensures (\null != msg_read_req && msg_read_request_bs__rvi <= msg_read_req->NoOfNodesToRead &&
  \null != msg_read_req->NodesToRead && \null != msg_read_request_bs__aid &&
  msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId \in {e_aid_NodeId, e_aid_NodeClass,
  e_aid_BrowseName, e_aid_DisplayName, e_aid_Value, e_aid_AccessLevel}) <==> *msg_read_request_bs__isvalid;
  @ ensures (\null != msg_read_req && msg_read_request_bs__rvi <= msg_read_req->NoOfNodesToRead &&
  \null != msg_read_req->NodesToRead) ==>
  is_correct_AttributeId(msg_read_req->NodesToRead[msg_read_request_bs__rvi-1].AttributeId, *msg_read_request_bs__aid);
  @ ensures (\null == msg_read_req || msg_read_request_bs__rvi > msg_read_req->NoOfNodesToRead || \null ==
  msg_read_req->NodesToRead) ==> *msg_read_request_bs__aid == constants__c_AttributeId_indet;
  @ ensures (\null == msg_read_req || msg_read_request_bs__rvi > msg_read_req->NoOfNodesToRead || \null ==
  msg_read_req->NodesToRead ||
  !is_correct_AttributeId(msg_read_req->NodesToRead[msg_read_request_bs__rvi-1].AttributeId, *msg_read_request_bs__aid))
  && bWarned == false ==> bWarned == true;
 */

static void s_getall_req_ReadValue_AttributeId(OpcUa_ReadRequest* msg_read_req,
                                               const constants__t_ReadValue_i msg_read_request_bs__rvi,
                                               constants__t_StatusCode_i* const msg_read_request_bs__sc,
                                               constants__t_AttributeId_i* const msg_read_request_bs__aid)
{
    *msg_read_request_bs__sc = constants__e_sc_ok;

    *msg_read_request_bs__aid = constants__c_AttributeId_indet;
    bool isvalid =
        s_AttributeId(msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].AttributeId, msg_read_request_bs__aid);

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
  @ requires \valid(msg_read_request_bs__isvalid);
  @ requires \valid(msg_read_request_bs__nid);
  @ requires msg_read_request_bs__rvi >= 1;
  @ requires msg_read_req != \null && msg_read_request_bs__rvi <= msg_read_req->NoOfNodesToRead &&
  msg_read_req->NodesToRead != \null ==> \valid(msg_read_req->NodesToRead+(msg_read_request_bs__rvi - 1));
  @ requires \separated(msg_read_request_bs__isvalid, msg_read_request_bs__nid, *msg_read_request_bs__nid, msg_read_req,
  msg_read_req->NodesToRead, msg_read_req->NodesToRead+(msg_read_request_bs__rvi - 1));
  @ assigns *msg_read_request_bs__isvalid;
  @ assigns *msg_read_request_bs__nid;
  @
  @ behavior valid:
  @     assumes msg_read_req != \null;
  @     assumes msg_read_request_bs__rvi <= msg_read_req->NoOfNodesToRead;
  @     assumes msg_read_req->NodesToRead != \null;
  @     ensures *msg_read_request_bs__isvalid == true;
  @     ensures *msg_read_request_bs__nid == &msg_read_req->NodesToRead[msg_read_request_bs__rvi - 1].NodeId;
  @
  @ behavior invalid:
  @     assumes msg_read_req == \null || msg_read_request_bs__rvi > msg_read_req->NoOfNodesToRead ||
  msg_read_req->NodesToRead == \null;
  @     ensures *msg_read_request_bs__nid == constants__c_NodeId_indet;
  @     ensures *msg_read_request_bs__isvalid == false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
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

/*@ requires pbttr == \null || \valid(pbttr);
  @ assigns *pbttr;
  @
  @ behavior valid_ptr:
  @ 	assumes pbttr != \null;
  @ 	ensures cttr == OpcUa_TimestampsToReturn_Source ==> *pbttr == constants__e_ttr_source;
  @ 	ensures cttr == OpcUa_TimestampsToReturn_Server ==> *pbttr == constants__e_ttr_server;
  @ 	ensures cttr == OpcUa_TimestampsToReturn_Both ==> *pbttr == constants__e_ttr_both;
  @ 	ensures cttr == OpcUa_TimestampsToReturn_Neither ==> *pbttr == constants__e_ttr_neither;
  @ 	ensures \result <==> (cttr \in {OpcUa_TimestampsToReturn_Source, OpcUa_TimestampsToReturn_Server,
  OpcUa_TimestampsToReturn_Both, OpcUa_TimestampsToReturn_Neither});
  @
  @ behavior invalid_ptr:
  @ 	assumes pbttr == \null;
  @ 	ensures \result == \false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */

static bool s_TimestampsToReturn(OpcUa_TimestampsToReturn cttr, constants__t_TimestampsToReturn_i* pbttr);

#ifndef __FRAMAC__
static bool s_TimestampsToReturn(OpcUa_TimestampsToReturn cttr, constants__t_TimestampsToReturn_i* pbttr)
{
    return util_TimestampsToReturn__C_to_B(cttr, pbttr);
}
#endif

/*@ requires \valid(msg_read_req);
  @ requires \valid(msg_read_request_bs__p_tsToReturn);
  @ requires \separated(msg_read_req, msg_read_request_bs__p_tsToReturn);
  @ assigns *msg_read_request_bs__p_tsToReturn;
  @ ensures \null == msg_read_req ==> *msg_read_request_bs__p_tsToReturn == constants__c_TimestampsToReturn_indet;
  @ ensures \null != msg_read_req && msg_read_req->TimestampsToReturn == OpcUa_TimestampsToReturn_Source ==>
  *msg_read_request_bs__p_tsToReturn == constants__e_ttr_source;
  @ ensures \null != msg_read_req && msg_read_req->TimestampsToReturn == OpcUa_TimestampsToReturn_Server ==>
  *msg_read_request_bs__p_tsToReturn == constants__e_ttr_server;
  @ ensures \null != msg_read_req && msg_read_req->TimestampsToReturn == OpcUa_TimestampsToReturn_Both ==>
  *msg_read_request_bs__p_tsToReturn == constants__e_ttr_both;
  @ ensures \null != msg_read_req && msg_read_req->TimestampsToReturn == OpcUa_TimestampsToReturn_Neither ==>
  *msg_read_request_bs__p_tsToReturn == constants__e_ttr_neither;
  @ ensures \null != msg_read_req && !(msg_read_req->TimestampsToReturn \in {OpcUa_TimestampsToReturn_Source,
  OpcUa_TimestampsToReturn_Server, OpcUa_TimestampsToReturn_Both, OpcUa_TimestampsToReturn_Neither}) ==>
  *msg_read_request_bs__p_tsToReturn == constants__c_TimestampsToReturn_indet;
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
  @ ensures *msg_read_request_bs__p_maxAge_valid <==> (\null != msg_read_req &&
  msg_read_req->MaxAge >= 0);
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
  @ ensures \null == msg_read_req ==> *msg_read_request_bs__nb == 0;
  @ ensures \null != msg_read_req ==>  *msg_read_request_bs__nb == msg_read_req->NoOfNodesToRead;
 */

static void s_read_req_nb_ReadValue(OpcUa_ReadRequest* msg_read_req, t_entier4* const msg_read_request_bs__nb)
{
    *msg_read_request_bs__nb = msg_read_req->NoOfNodesToRead;
}

#ifndef __FRAMAC__
void msg_read_request_bs__read_req_nb_ReadValue(const constants__t_msg_i msg_read_request_bs__msg,
                                                t_entier4* const msg_read_request_bs__nb)
{
    OpcUa_ReadRequest* msg_read_req = (OpcUa_ReadRequest*) msg_read_request_bs__msg;

    s_read_req_nb_ReadValue(msg_read_req, msg_read_request_bs__nb);
}
#endif // __FRAMAC__
