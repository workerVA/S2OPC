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

#ifndef UTIL_B2C_H_
#define UTIL_B2C_H_

#include <stdbool.h>

#include "address_space_impl.h"
#include "constants.h"
#include "opcua_statuscodes.h"
#include "sopc_encodeable.h"
#include "sopc_types.h"

void util_message__get_encodeable_type(const constants__t_msg_type_i message__msg_type,
                                       SOPC_EncodeableType** reqEncType,
                                       SOPC_EncodeableType** respEncType,
                                       t_bool* isRequest);

void util_message__get_message_type(SOPC_EncodeableType* encType, constants__t_msg_type_i* message__msg_type);

/*@ requires \valid(status);
  @ assigns *status;
 */

void util_status_code__B_to_C(constants__t_StatusCode_i bstatus, SOPC_StatusCode* status);

/*@ requires \valid(bstatus);
  @ assigns *bstatus;
 */

void util_status_code__C_to_B(SOPC_StatusCode status, constants__t_StatusCode_i* bstatus);

SOPC_ReturnStatus util_status_code__B_to_return_status_C(constants__t_StatusCode_i bstatus);

bool util_channel__SecurityPolicy_C_to_B(const char* uri, constants__t_SecurityPolicy* secpol);

/* Returns true or false upon failure (e_bd_indet or invalid cdir) */
bool util_BrowseDirection__B_to_C(constants__t_BrowseDirection_i bdir, OpcUa_BrowseDirection* cdir);

/*@ requires bdir == \null || \valid(bdir);
  @ assigns *bdir;
  @
  @ behavior valid_ptr:
  @     assumes bdir != \null;
  @     ensures cdir == OpcUa_BrowseDirection_Forward ==> *bdir == constants__e_bd_forward;
  @     ensures cdir == OpcUa_BrowseDirection_Inverse ==> *bdir == constants__e_bd_inverse;
  @     ensures cdir == OpcUa_BrowseDirection_Both ==> *bdir == constants__e_bd_both;
  @     ensures \result <==> (cdir \in {OpcUa_BrowseDirection_Forward, OpcUa_BrowseDirection_Inverse,
  OpcUa_BrowseDirection_Both});
  @     ensures !(cdir \in {OpcUa_BrowseDirection_Forward, OpcUa_BrowseDirection_Inverse,
  OpcUa_BrowseDirection_Both}) ==> *bdir == \at(*bdir, Pre);
  @
  @ behavior invalid_ptr:
  @     assumes bdir == \null;
  @     ensures \result == \false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */

/* Returns true or false upon failure (invalid bdir) */
bool util_BrowseDirection__C_to_B(OpcUa_BrowseDirection cdir, constants__t_BrowseDirection_i* bdir);

/* Returns true or false upon failure (c_NodeClass_indet or invalid cncl) */
bool util_NodeClass__B_to_C(constants__t_NodeClass_i bncl, OpcUa_NodeClass* cncl);

/* Returns true or false upon failure (invalid bncl) */
bool util_NodeClass__C_to_B(OpcUa_NodeClass cncl, constants__t_NodeClass_i* bncl);

/* Returns true or false upon failure (c_TimestampsToReturn_indet or invalid pcttr) */
bool util_TimestampsToReturn__B_to_C(constants__t_TimestampsToReturn_i bttr, OpcUa_TimestampsToReturn* pcttr);

/*@ requires \true;
  @ assigns \nothing;
  @ ensures cttr == OpcUa_TimestampsToReturn_Source ==> \result == constants__e_ttr_source;
  @ ensures cttr == OpcUa_TimestampsToReturn_Server ==> \result == constants__e_ttr_server;
  @ ensures cttr == OpcUa_TimestampsToReturn_Both ==> \result == constants__e_ttr_both;
  @ ensures cttr == OpcUa_TimestampsToReturn_Neither ==> \result == constants__e_ttr_neither;
  @ ensures !(cttr \in {OpcUa_TimestampsToReturn_Source, OpcUa_TimestampsToReturn_Server, OpcUa_TimestampsToReturn_Both,
  OpcUa_TimestampsToReturn_Neither}) ==> \result == constants__c_TimestampsToReturn_indet;
 */

/* Returns B enum value corresponding to C enum value of timestamps to return */
constants__t_TimestampsToReturn_i util_TimestampsToReturn__C_to_B(OpcUa_TimestampsToReturn cttr);

/* Returns true or false upon failure (c_AttributeId_indet or invalid pcaid) */
bool util_AttributeId__B_to_C(constants__t_AttributeId_i baid, uint32_t* pcaid);

/*@ requires pbaid == \null || \valid(pbaid);
  @ assigns *pbaid;
  @
  @ behavior valid_ptr:
  @     assumes pbaid != \null;
  @     ensures caid == e_aid_NodeId ==> *pbaid == constants__e_aid_NodeId;
  @     ensures caid == e_aid_NodeClass ==> *pbaid == constants__e_aid_NodeClass;
  @     ensures caid == e_aid_BrowseName ==> *pbaid == constants__e_aid_BrowseName;
  @     ensures caid == e_aid_DisplayName ==> *pbaid == constants__e_aid_DisplayName;
  @     ensures caid == e_aid_Value ==> *pbaid == constants__e_aid_Value;
  @     ensures caid == e_aid_AccessLevel ==> *pbaid == constants__e_aid_AccessLevel;
  @     ensures \result <==> caid \in {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value,
  e_aid_AccessLevel};
  @     ensures !(caid \in {e_aid_NodeId, e_aid_NodeClass, e_aid_BrowseName, e_aid_DisplayName, e_aid_Value,
  e_aid_AccessLevel}) ==> *pbaid == \at(*pbaid, Pre);
  @
  @ behavior invalid_ptr:
  @     assumes pbaid == \null;
  @     ensures \result == \false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */

/* Returns true or false upon failure (invalid caid or invalid pbaid) */
bool util_AttributeId__C_to_B(uint32_t caid, constants__t_AttributeId_i* pbaid);

#endif /* UTIL_B2C_H */
