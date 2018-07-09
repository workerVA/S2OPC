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
 * Implements the structures behind the address space.
 */

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "b2c.h"
#include "response_write_bs.h"

#include "frama_c_assert.h"
#include "util_b2c.h"

#include "sopc_services_api.h"
#include "sopc_toolkit_config_internal.h"
#include "sopc_toolkit_constants.h"
#include "sopc_types.h"

/* Globals */
static SOPC_StatusCode* arr_StatusCode; /* Indexed from 1, first element is never used. */
static t_entier4 nb_req;

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void response_write_bs__INITIALISATION(void)
{
    arr_StatusCode = NULL;
    nb_req = 0;
}

/*--------------------
   OPERATIONS Clause
  --------------------*/

/*@ assigns \result;
  @ ensures \result == NULL || \valid((SOPC_StatusCode*)\result+(0 .. nb-1));
 */

static SOPC_StatusCode* statuscode_malloc(size_t size, int nb)
{
    return (SOPC_StatusCode*) malloc(size);
}

/*@ requires \valid(response_write_bs__ResponseWrite_allocated);
  @ requires response_write_bs__nb_req >= 0;
  @ assigns nb_req;
  @ assigns arr_StatusCode;
  @ assigns *response_write_bs__ResponseWrite_allocated;
  @
  @ behavior has_allocated:
  @ 	assumes (uint64_t) response_write_bs__nb_req + 1 <= (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode);
  @ 	assigns arr_StatusCode[0 .. response_write_bs__nb_req];
  @ 	ensures \false;
  @ 	ensures \null == arr_StatusCode || \valid(arr_StatusCode+(0 .. response_write_bs__nb_req)) ;
  @ 	ensures \null != arr_StatusCode ==> \forall integer x; 0 <= x <= response_write_bs__nb_req ==>
  arr_StatusCode[x] == OpcUa_BadInternalError;
  @ 	ensures \null != arr_StatusCode ==> *response_write_bs__ResponseWrite_allocated == true;
  @ 	ensures \null != arr_StatusCode ==> nb_req == response_write_bs__nb_req;
  @ 	ensures \null == arr_StatusCode ==> *response_write_bs__ResponseWrite_allocated == false;
  @ 	ensures \null == arr_StatusCode ==> nb_req == 0;
  @
  @ behavior not_allocated:
  @ 	assumes (uint64_t) response_write_bs__nb_req + 1 > (uint64_t) SIZE_MAX /
  sizeof(SOPC_StatusCode);
  @ 	ensures \false;
  @ 	ensures arr_StatusCode == \null;
  @ 	ensures *response_write_bs__ResponseWrite_allocated == false;
  @ 	ensures nb_req == 0;
  @
  @ disjoint behaviors;
  @ complete behaviors;
 */

/* Can response_write_bs__nb_req be at MAX_INT ?
 * Can we suppose that response_write_bs__nb_req will never be negative normally ?*/

void response_write_bs__alloc_write_request_responses_malloc(const t_entier4 response_write_bs__nb_req,
                                                             t_bool* const response_write_bs__ResponseWrite_allocated)
{
    *response_write_bs__ResponseWrite_allocated = false; /* TODO: set a true and false in b2c.h */
    nb_req = 0;

    if (response_write_bs__nb_req >= 0 &&
        (uint64_t) response_write_bs__nb_req + 1 <= (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode))
    {
        arr_StatusCode = statuscode_malloc(sizeof(SOPC_StatusCode) * (size_t)(response_write_bs__nb_req + 1),
                                           response_write_bs__nb_req + 1);
    }
    else
    {
        arr_StatusCode = NULL;
    }
    if (NULL != arr_StatusCode)
    {
        /*@ loop invariant 0 <= i <= response_write_bs__nb_req+1;
          @ loop invariant \forall integer x; 0 <= x < i ==> arr_StatusCode[x] == OpcUa_BadInternalError;
          @ loop assigns i, arr_StatusCode[0 .. (i-1)];
          @ loop variant response_write_bs__nb_req + 1 - i;
         */

        for (int32_t i = 0; i <= response_write_bs__nb_req; i++)
        {
            arr_StatusCode[i] = OpcUa_BadInternalError;
        }
        *response_write_bs__ResponseWrite_allocated = true;
        nb_req = response_write_bs__nb_req;
    }
}

/*@ requires (void*)arr_StatusCode == \null || \true;
  //freeable is not implemented still
  @ frees arr_StatusCode;
  @ assigns nb_req;
  @ assigns arr_StatusCode;
  @ assigns __fc_heap_status;
  @ ensures nb_req == 0;
  @ ensures arr_StatusCode == \null;
 */

void response_write_bs__reset_ResponseWrite(void)
{
    //@ assert (void*)arr_StatusCode == \null || \true;
    // freeable is not implemented still
    free(arr_StatusCode);
    arr_StatusCode = NULL;
    nb_req = 0;
}

/*@ requires \valid(arr_StatusCode + (response_write_bs__wvi));
  @ requires response_write_bs__wvi >= 0;
  @ assigns arr_StatusCode[response_write_bs__wvi];
 */

void response_write_bs__set_ResponseWrite_StatusCode(const constants__t_WriteValue_i response_write_bs__wvi,
                                                     const constants__t_StatusCode_i response_write_bs__sc)
{
    util_status_code__B_to_C(response_write_bs__sc, &arr_StatusCode[response_write_bs__wvi]);
}

/*@ requires \valid(msg_write_resp);
  @ requires (nb_req > 0 && (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) >= (uint64_t) nb_req)
  ==> (\valid(arr_StatusCode) && \valid(arr_StatusCode+(1..nb_req)));
  @ assigns msg_write_resp->NoOfResults;
  @ assigns msg_write_resp->Results;
  @ assigns msg_write_resp->Results[0 .. (sizeof(SOPC_StatusCode) * (size_t) nb_req)];
  @ assigns msg_write_resp->NoOfDiagnosticInfos;
  @ assigns msg_write_resp->DiagnosticInfos;
  @ ensures msg_write_resp->NoOfDiagnosticInfos == 0;
  @ ensures msg_write_resp->DiagnosticInfos == \null;
  @ ensures msg_write_resp->Results != \null ==> \forall integer x; 1 <= x <= nb_req ==> msg_write_resp->Results[x] ==
  arr_StatusCode[x];
  @ ensures msg_write_resp->Results != \null ==> msg_write_resp->NoOfResults == nb_req;
  @ ensures msg_write_resp->Results == \null ==> msg_write_resp->NoOfResults == 0;
 */

void s_write_WriteResponse_msg_out(OpcUa_WriteResponse* msg_write_resp)
{
    SOPC_StatusCode* lsc = NULL;

    if (nb_req > 0 && (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) >= (uint64_t) nb_req)
    {
        lsc = (SOPC_StatusCode*) malloc(sizeof(SOPC_StatusCode) * (size_t) nb_req);
    }

    if (NULL == lsc)
    {
        // TODO: report memory error
        msg_write_resp->NoOfResults = 0;
    }
    else
    {
        memcpy(lsc, (void*) (arr_StatusCode + 1), sizeof(SOPC_StatusCode) * (size_t) nb_req);

        msg_write_resp->NoOfResults = nb_req;
    }

    msg_write_resp->Results = lsc;
    msg_write_resp->NoOfDiagnosticInfos = 0;
    msg_write_resp->DiagnosticInfos = NULL;
}

void response_write_bs__write_WriteResponse_msg_out(const constants__t_msg_i response_write_bs__msg_out)
{
    assert(*(SOPC_EncodeableType**) response_write_bs__msg_out == &OpcUa_WriteRequest_EncodeableType);

    OpcUa_WriteResponse* msg_write_resp = (OpcUa_WriteResponse*) response_write_bs__msg_out;

    s_write_WriteResponse_msg_out(msg_write_resp);
}
