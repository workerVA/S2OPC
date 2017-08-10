/*
 *  Copyright (C) 2017 Systerel and others.
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
 * Implements the structures behind the address space.
 */


#include "b2c.h"
#include "service_get_endpoints_bs.h"

#include "sopc_sc_events.h"
#include "sopc_types.h"

#include <stdbool.h>
#include <assert.h>

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void service_get_endpoints_bs__INITIALISATION(void)
{
}

/*--------------------
   OPERATIONS Clause
  --------------------*/
void service_get_endpoints_bs__treat_get_endpoints_request(
   const constants__t_msg_i service_get_endpoints_bs__req_msg,
   const constants__t_msg_i service_get_endpoints_bs__resp_msg,
   const constants__t_endpoint_config_idx_i service_get_endpoints_bs__endpoint_config_idx,
   constants__t_StatusCode_i * const service_get_endpoints_bs__ret){
  SOPC_Toolkit_Msg* reqMsg = (SOPC_Toolkit_Msg*) service_get_endpoints_bs__req_msg;
  SOPC_Toolkit_Msg* respMsg = (SOPC_Toolkit_Msg*) service_get_endpoints_bs__resp_msg;
  OpcUa_GetEndpointsRequest* getEndpointsReq = (OpcUa_GetEndpointsRequest*) reqMsg->msgStruct;
  OpcUa_GetEndpointsResponse* getEndpointsResp = (OpcUa_GetEndpointsResponse*) respMsg->msgStruct;
  uint32_t configIdx = (uint32_t) service_get_endpoints_bs__endpoint_config_idx;
  (void) getEndpointsReq;
  (void) getEndpointsResp;
  (void) configIdx;
  *service_get_endpoints_bs__ret = constants__e_sc_nok;
}


