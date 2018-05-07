/*
 *  Copyright (C) 2018 Systerel and others.
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as
 *  published by the Free Software Foundation, either version 3 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

/** \file
 *
 * Hand-modified _bs.h to specify my own # defines
 */

#ifndef CONSTANTS_BS_H_
#define CONSTANTS_BS_H_

#include <stdint.h>
#include <stdlib.h>

/*--------------------------
   Added by the Translator
  --------------------------*/
#include "b2c.h"

#include "sopc_address_space.h"
#include "sopc_builtintypes.h"
#include "sopc_types.h"

/*-----------------------------
   SETS Clause: deferred sets
  -----------------------------*/
typedef SOPC_ExpandedNodeId* constants_bs__t_ExpandedNodeId_i;
typedef SOPC_LocalizedText* constants_bs__t_LocalizedText_i;
typedef SOPC_NodeId* constants_bs__t_NodeId_i;
typedef SOPC_AddressSpace_Item* constants_bs__t_Node_i;
typedef SOPC_ByteString* constants_bs__t_Nonce_i;
typedef SOPC_QualifiedName* constants_bs__t_QualifiedName_i;
typedef OpcUa_ReferenceNode* constants_bs__t_Reference_i;
typedef OpcUa_SignatureData* constants_bs__t_SignatureData_i;
typedef SOPC_Variant* constants_bs__t_Variant_i;
typedef OpcUa_WriteValue* constants_bs__t_WriteValuePointer_i;
typedef uintptr_t constants_bs__t_application_context_i;
typedef SOPC_Buffer* constants_bs__t_byte_buffer_i;
typedef uint32_t constants_bs__t_channel_config_idx_i;
typedef uint32_t constants_bs__t_channel_i;
typedef uint32_t constants_bs__t_client_request_handle_i;
typedef uint32_t constants_bs__t_endpoint_config_idx_i;
typedef void* constants_bs__t_msg_header_i;
typedef void* constants_bs__t_msg_i;
typedef uint32_t constants_bs__t_request_context_i;
typedef uint32_t constants_bs__t_server_request_handle_i;
typedef uint32_t constants_bs__t_session_i;
typedef SOPC_NodeId* constants_bs__t_session_token_i;
#define constants_bs__t_user_i t_entier4

/*--------------------------
   Added by the Translator
  --------------------------*/
#define constants_bs__t_ExpandedNodeId_i_max (-1)
#define constants_bs__t_LocalizedText_i_max (-1)
#define constants_bs__t_NodeId_i_max (-1)
#define constants_bs__t_Node_i_max (-1)
#define constants_bs__t_Nonce_i_max (-1)
#define constants_bs__t_QualifiedName_i_max (-1)
#define constants_bs__t_Reference_i_max (-1)
#define constants_bs__t_SignatureData_i_max (-1)
#define constants_bs__t_Variant_i_max (-1)
#define constants_bs__t_application_context_i_max (-1)
#define constants_bs__t_byte_buffer_i_max (-1)
#define constants_bs__t_channel_config_idx_i_max (2 * SOPC_MAX_SECURE_CONNECTIONS)
#define constants_bs__t_channel_i_max SOPC_MAX_SECURE_CONNECTIONS
#define constants_bs__t_client_request_handle_i_max (-1)
#define constants_bs__t_endpoint_config_idx_i_max SOPC_MAX_ENDPOINT_DESCRIPTION_CONFIGURATIONS
#define constants_bs__t_msg_header_i_max (-1)
#define constants_bs__t_msg_i_max (-1)
#define constants_bs__t_request_context_i_max (-1)
#define constants_bs__t_server_request_handle_i_max (-1)
#define constants_bs__t_session_i_max SOPC_MAX_SESSIONS
#define constants_bs__t_session_token_i_max (-1)
#define constants_bs__t_user_i_max (-1)

/*------------------------------------------------
   CONCRETE_CONSTANTS Clause: scalars and arrays
  ------------------------------------------------*/
#define constants_bs__c_ExpandedNodeId_indet NULL
#define constants_bs__c_LocalizedText_indet 0
#define constants_bs__c_NodeId_indet 0
#define constants_bs__c_Node_indet 0
#define constants_bs__c_Nonce_indet 0
#define constants_bs__c_QualifiedName_indet 0
#define constants_bs__c_Reference_indet 0
#define constants_bs__c_SignatureData_indet 0
#define constants_bs__c_Variant_indet 0
#define constants_bs__c_byte_buffer_indet 0
#define constants_bs__c_channel_config_idx_indet 0
#define constants_bs__c_channel_indet 0
#define constants_bs__c_client_request_handle_indet 0
#define constants_bs__c_endpoint_config_idx_indet 0
#define constants_bs__c_msg_header_indet 0
#define constants_bs__c_msg_indet 0
#define constants_bs__c_no_application_context 0
#define constants_bs__c_request_context_indet 0
#define constants_bs__c_session_indet 0
#define constants_bs__c_session_token_indet 0
#define constants_bs__c_user_indet 0
#define constants_bs__k_n_BrowseResponse_max SOPC_MAX_OPERATIONS_PER_MSG
#define constants_bs__k_n_BrowseTarget_max SOPC_MAX_OPERATIONS_PER_MSG
#define constants_bs__k_n_WriteResponse_max SOPC_MAX_OPERATIONS_PER_MSG
#define constants_bs__k_n_read_resp_max SOPC_MAX_OPERATIONS_PER_MSG

/*------------------------
   INITIALISATION Clause
  ------------------------*/
extern void constants_bs__INITIALISATION(void);

/*--------------------
   OPERATIONS Clause
  --------------------*/
extern void constants_bs__get_Is_SubType(const constants_bs__t_NodeId_i constants_bs__p_type1,
                                         const constants_bs__t_NodeId_i constants_bs__p_type2,
                                         t_bool* const constants_bs__p_res);
extern void constants_bs__get_card_t_channel(t_entier4* const constants_bs__p_card_channel);
extern void constants_bs__get_card_t_session(t_entier4* const constants_bs__p_card_session);
extern void constants_bs__get_cast_t_channel(const t_entier4 constants_bs__p_ind,
                                             constants_bs__t_channel_i* const constants_bs__p_channel);
extern void constants_bs__get_cast_t_session(const t_entier4 constants_bs__p_ind,
                                             constants_bs__t_session_i* const constants_bs__p_session);
extern void constants_bs__getall_conv_ExpandedNodeId_NodeId(
    const constants_bs__t_ExpandedNodeId_i constants_bs__p_expnid,
    t_bool* const constants_bs__p_isvalid,
    constants_bs__t_NodeId_i* const constants_bs__p_nid);
extern void constants_bs__is_t_channel(const constants_bs__t_channel_i constants_bs__p_channel,
                                       t_bool* const constants_bs__p_res);
extern void constants_bs__is_t_channel_config_idx(const constants_bs__t_channel_config_idx_i constants_bs__p_config_idx,
                                                  t_bool* const constants_bs__p_res);
extern void constants_bs__is_t_endpoint_config_idx(
    const constants_bs__t_endpoint_config_idx_i constants_bs__p_endpoint_config_idx,
    t_bool* const constants_bs__p_res);

#endif
