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
 * Implements the base machine for the constants
 */

#include "constants_bs.h"
#include "b2c.h"

#include "sopc_types.h"

void constants_bs__INITIALISATION(void) {}

/*--------------------
   OPERATIONS Clause
  --------------------*/

/*@ predicate is_NodeId_Subtype(constants_bs__t_NodeId_i type1, constants_bs__t_NodeId_i type2) =
  @  //TODO implement this when the subtype query is functional
  @ \true;
 */

/*@ requires \valid(constants_bs__p_res);
  @ assigns *constants_bs__p_res;
  @ ensures *constants_bs__p_res <==> is_NodeId_Subtype(constants_bs__p_type1, constants_bs__p_type2);
 */

void constants_bs__get_Is_SubType(const constants_bs__t_NodeId_i constants_bs__p_type1,
                                  const constants_bs__t_NodeId_i constants_bs__p_type2,
                                  t_bool* const constants_bs__p_res)
{
    (void) constants_bs__p_type1;
    (void) constants_bs__p_type2;
    /* TODO: implement a functional subtype query */
    *constants_bs__p_res = true;
}

/*@ requires \valid(constants_bs__p_nid);
  @ requires \valid_read(constants_bs__p_expnid);
  @ assigns *constants_bs__p_nid;
  @ ensures *constants_bs__p_nid == &constants_bs__p_expnid->NodeId;
 */
void constants_bs__getall_conv_ExpandedNodeId_NodeId(const constants_bs__t_ExpandedNodeId_i constants_bs__p_expnid,
                                                     constants_bs__t_NodeId_i* const constants_bs__p_nid)
{
    /* Reminder: This is a borrow */
    *constants_bs__p_nid = &constants_bs__p_expnid->NodeId;
}

/*@ requires \valid(constants_bs__p_card_channel);
  @ assigns *constants_bs__p_card_channel;
  @ ensures *constants_bs__p_card_channel == constants_bs__t_channel_i_max;
 */

void constants_bs__get_card_t_channel(t_entier4* const constants_bs__p_card_channel)
{
    *constants_bs__p_card_channel = constants_bs__t_channel_i_max;
}

/*@ requires \valid(constants_bs__p_card_session);
  @ assigns *constants_bs__p_card_session;
  @ ensures *constants_bs__p_card_session == constants_bs__t_session_i_max;
 */

void constants_bs__get_card_t_session(t_entier4* const constants_bs__p_card_session)
{
    *constants_bs__p_card_session = constants_bs__t_session_i_max;
}

/*@ requires \valid(constants_bs__p_card_subscription);
  @ assigns *constants_bs__p_card_subscription;
  @ ensures *constants_bs__p_card_subscription == constants_bs__t_subscription_i_max;
 */

void constants_bs__get_card_t_subscription(t_entier4* const constants_bs__p_card_subscription)
{
    *constants_bs__p_card_subscription = constants_bs__t_subscription_i_max;
}

/*@ requires \valid(constants_bs__p_channel);
  @ requires constants_bs__p_ind != constants_bs__c_channel_indet;
  @ requires constants_bs__p_ind >= 0;
  @ assigns *constants_bs__p_channel;
  @ ensures *constants_bs__p_channel == (uint32_t) constants_bs__p_ind;
 */

void constants_bs__get_cast_t_channel(const t_entier4 constants_bs__p_ind,
                                      constants_bs__t_channel_i* const constants_bs__p_channel)
{
    *constants_bs__p_channel = (uint32_t) constants_bs__p_ind;
}

/*@ requires \valid(constants_bs__p_session);
  @ requires constants_bs__p_ind != constants_bs__c_session_indet;
  @ requires constants_bs__p_ind >= 0;
  @ assigns *constants_bs__p_session;
  @ ensures *constants_bs__p_session == (uint32_t) constants_bs__p_ind;
 */

void constants_bs__get_cast_t_session(const t_entier4 constants_bs__p_ind,
                                      constants_bs__t_session_i* const constants_bs__p_session)
{
    *constants_bs__p_session = (uint32_t) constants_bs__p_ind;
}

/*@ requires \valid(constants_bs__p_subscription);
  @ requires constants_bs__p_ind != constants_bs__c_subscription_indet;
  @ requires constants_bs__p_ind >= 0;
  @ assigns *constants_bs__p_subscription;
  @ ensures *constants_bs__p_subscription == (uint32_t) constants_bs__p_ind;
 */

void constants_bs__get_cast_t_subscription(const t_entier4 constants_bs__p_ind,
                                           constants_bs__t_subscription_i* const constants_bs__p_subscription)
{
    *constants_bs__p_subscription = (uint32_t) constants_bs__p_ind;
}

/*@ requires \valid(constants_bs__p_res);
  @ assigns *constants_bs__p_res;
  @ ensures *constants_bs__p_res <==> (constants_bs__c_channel_indet != constants_bs__p_channel &&
  constants_bs__p_channel > 0 && constants_bs__p_channel <= constants_bs__t_channel_i_max);
 */

void constants_bs__is_t_channel(const constants_bs__t_channel_i constants_bs__p_channel,
                                t_bool* const constants_bs__p_res)
{
    *constants_bs__p_res = (constants_bs__c_channel_indet != constants_bs__p_channel && constants_bs__p_channel > 0 &&
                            constants_bs__p_channel <= constants_bs__t_channel_i_max);
}

/*@ requires \valid(constants_bs__p_res);
  @ assigns *constants_bs__p_res;
  @ ensures *constants_bs__p_res <==> (constants_bs__c_channel_config_idx_indet != constants_bs__p_config_idx &&
  constants_bs__p_config_idx > 0 && constants_bs__p_config_idx <= constants_bs__t_channel_config_idx_i_max);
 */

void constants_bs__is_t_channel_config_idx(const constants_bs__t_channel_config_idx_i constants_bs__p_config_idx,
                                           t_bool* const constants_bs__p_res)
{
    *constants_bs__p_res =
        (constants_bs__c_channel_config_idx_indet != constants_bs__p_config_idx && constants_bs__p_config_idx > 0 &&
         constants_bs__p_config_idx <= constants_bs__t_channel_config_idx_i_max);
}

/*@ requires \valid(constants_bs__p_res);
  @ assigns *constants_bs__p_res;
  @ ensures *constants_bs__p_res <==> (constants_bs__p_endpoint_config_idx != constants_bs__c_endpoint_config_idx_indet
  && constants_bs__p_endpoint_config_idx > 0 && constants_bs__p_endpoint_config_idx <=
  constants_bs__t_endpoint_config_idx_i_max);
 */

void constants_bs__is_t_endpoint_config_idx(
    const constants_bs__t_endpoint_config_idx_i constants_bs__p_endpoint_config_idx,
    t_bool* const constants_bs__p_res)
{
    *constants_bs__p_res = (constants_bs__p_endpoint_config_idx != constants_bs__c_endpoint_config_idx_indet &&
                            constants_bs__p_endpoint_config_idx > 0 &&
                            constants_bs__p_endpoint_config_idx <= constants_bs__t_endpoint_config_idx_i_max);
}
