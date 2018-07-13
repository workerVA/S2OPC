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

/*@ axiomatic malloc_prop
  @ {
  @ 	predicate is_malloc_result(SOPC_StatusCode* p, integer n);
  @ 	axiom S : \forall integer n, SOPC_StatusCode* p1, t_bool* p2; is_malloc_result(p1, n) ==>
  \separated(p1+(0 .. n), p2);
  @
  @ 	predicate is_malloc_separated(SOPC_StatusCode* p1, SOPC_StatusCode* p2, integer n);
  @ 	axiom T : \forall integer n, SOPC_StatusCode* p1, SOPC_StatusCode* p2; is_malloc_separated(p1, p2, n) ==>
  \separated(p1+(0 .. n), p2+(0 .. n));
  @ }
 */

/*@ ghost int has_mem; */

/*@ assigns \result;
  @ assigns \result \from size, nb;
  @ behavior allocated:
  @     assumes has_mem;
  @     ensures \valid(\result + (0 .. nb-1));
  @ 	ensures is_malloc_result(\result, nb - 1);
  @ 	ensures is_malloc_separated(\result, arr_StatusCode+1, nb-1); //Bourrin, a changer
  @
  @ behavior not_allocated:
  @ 	assumes !has_mem;
  @     ensures \result == \null;
  @
  @ disjoint behaviors;
  @ complete behaviors;

*/

static SOPC_StatusCode* statuscode_malloc(size_t size, size_t nb);

#ifndef __FRAMAC__
static SOPC_StatusCode* statuscode_malloc(size_t size, size_t nb)
{
    return (SOPC_StatusCode*) malloc(size * nb);
}
#endif // __FRAMAC__

/*@ requires \valid(response_write_bs__ResponseWrite_allocated);
  @ requires response_write_bs__nb_req >= 0;
  @ assigns nb_req;
  @ assigns arr_StatusCode;
  @ assigns \at(arr_StatusCode[0 .. response_write_bs__nb_req], Post);
  @ assigns *response_write_bs__ResponseWrite_allocated;
  @ ensures \false;
  @ behavior has_allocated:
  @ 	assumes (uint64_t) response_write_bs__nb_req + 1 <= (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) && has_mem;
  @ 	ensures \forall integer y; 0 <= y <= response_write_bs__nb_req ==> arr_StatusCode[y] == OpcUa_BadInternalError;
  @ 	ensures *response_write_bs__ResponseWrite_allocated == true;
  @ 	ensures nb_req == response_write_bs__nb_req;
  @
  @ behavior not_allocated:
  @ 	assumes (uint64_t) response_write_bs__nb_req + 1 > (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) || !has_mem;
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
        arr_StatusCode = statuscode_malloc(sizeof(SOPC_StatusCode), (size_t) response_write_bs__nb_req + 1);
    }
    else
    {
        arr_StatusCode = NULL;
    }

    /*@ assigns nb_req;
      @ assigns arr_StatusCode[0 .. response_write_bs__nb_req];
      @ assigns *response_write_bs__ResponseWrite_allocated;
      @
      @ behavior sub_has_allocated:
      @ 	assumes (uint64_t) response_write_bs__nb_req + 1 <= (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) &&
      has_mem;
      @ 	ensures *response_write_bs__ResponseWrite_allocated == true;
      @ 	ensures \forall integer z; 0 <= z < response_write_bs__nb_req + 1 ==> arr_StatusCode[z] ==
      OpcUa_BadInternalError;
      @ 	ensures nb_req == response_write_bs__nb_req;
      @
      @ behavior sub_not_allocated:
      @ 	assumes (uint64_t) response_write_bs__nb_req + 1 > (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) ||
      !has_mem;
      @ 	ensures arr_StatusCode == \null;
      @ 	ensures *response_write_bs__ResponseWrite_allocated == false;
      @ 	ensures nb_req == 0;
      @
      @ disjoint behaviors;
      @ complete behaviors;
    */
    if (NULL != arr_StatusCode)
    {
        /*@ loop invariant 0 <= i <= response_write_bs__nb_req + 1;
          @ loop invariant \forall integer x; 0 <= x < i ==> arr_StatusCode[x] == OpcUa_BadInternalError;
          @ loop assigns i, arr_StatusCode[0 .. response_write_bs__nb_req];
          @ loop variant response_write_bs__nb_req + 1 - i;
         */
        for (int32_t i = 0; i < response_write_bs__nb_req + 1; i++)
        {
            arr_StatusCode[i] = OpcUa_BadInternalError;
        }
        nb_req = response_write_bs__nb_req;
        *response_write_bs__ResponseWrite_allocated = true;
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

/*@ requires \valid(p1+(0 .. nb - 1));
  @ requires \valid_read(p2+(0 .. nb - 1));
  @ requires \separated(p1+(0 .. nb - 1), p2+(0 .. nb - 1));
  @ assigns p1[0 .. nb - 1];
  @ ensures \forall integer i; 0 <= i < nb ==> p1[i] == p2[i];
 */

static SOPC_StatusCode* statuscode_memcpy(SOPC_StatusCode* p1, const SOPC_StatusCode* p2, size_t size, size_t nb);

#ifndef __FRAMAC__
static void statuscode_memcpy(SOPC_StatusCode* p1, const SOPC_StatusCode* p2, size_t size, size_t nb)
{
    (SOPC_StatusCode*) memcpy(p1, (void*) p2, size * nb);
}
#endif

/*@ requires \valid(msg_write_resp);
  @ requires (nb_req > 0 && (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) >= (uint64_t) nb_req)
  ==> (\valid_read(arr_StatusCode) && \valid_read(arr_StatusCode+(1..nb_req)));
  @ assigns msg_write_resp->NoOfResults;
  @ assigns msg_write_resp->Results;
  @ assigns msg_write_resp->NoOfDiagnosticInfos;
  @ assigns msg_write_resp->DiagnosticInfos;
  @ assigns msg_write_resp->Results[0 .. nb_req - 1];
  @ assigns \at(msg_write_resp->Results[0 .. nb_req - 1], Post);
  @
  @ behavior has_allocated:
  @ 	assumes nb_req > 0 && (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) >= (uint64_t) nb_req && has_mem;
  @ 	ensures msg_write_resp->NoOfDiagnosticInfos == 0;
  @ 	ensures msg_write_resp->DiagnosticInfos == \null;
  @ 	ensures msg_write_resp->NoOfResults == nb_req;
  @ 	ensures \forall integer i; 0 <= i < nb_req ==> msg_write_resp->Results[i] == arr_StatusCode[i+1];
  @
  @ behavior not_allocated:
  @ 	assumes nb_req <= 0 || (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) < (uint64_t) nb_req || !has_mem;
  @ 	ensures msg_write_resp->NoOfDiagnosticInfos == 0;
  @ 	ensures msg_write_resp->DiagnosticInfos == \null;
  @ 	ensures msg_write_resp->NoOfResults == 0;
  @ 	ensures msg_write_resp->Results == \null;
  @
  @ complete behaviors;
  @ disjoint behaviors;
 */

void s_write_WriteResponse_msg_out(OpcUa_WriteResponse* msg_write_resp)
{
    SOPC_StatusCode* lsc = NULL;

    if (nb_req > 0 && (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) >= (uint64_t) nb_req)
    {
        lsc = (SOPC_StatusCode*) statuscode_malloc(sizeof(SOPC_StatusCode), (size_t) nb_req);
    }
    /*@ assigns msg_write_resp->NoOfResults;
      @ assigns lsc[0 .. nb_req-1];
      @
      @ behavior A:
      @ 	assumes nb_req > 0 && (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) >= (uint64_t) nb_req && has_mem;
      @ 	ensures \forall integer i; 0 <= i < nb_req ==> msg_write_resp->Results[i] == arr_StatusCode[i+1];
      @ 	ensures msg_write_resp->NoOfResults == nb_req;
      @
      @ behavior B:
      @ 	assumes nb_req <= 0 || (uint64_t) SIZE_MAX / sizeof(SOPC_StatusCode) < (uint64_t) nb_req || !has_mem;
      @ 	ensures msg_write_resp->NoOfResults == 0;
      @
      @ complete behaviors;
      @ disjoint behaviors;
     */
    if (NULL == lsc)
    {
        // TODO: report memory error
        msg_write_resp->NoOfResults = 0;
    }
    else
    {
        msg_write_resp->NoOfResults = nb_req;

        statuscode_memcpy(lsc, (arr_StatusCode + 1), sizeof(SOPC_StatusCode), nb_req);
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
