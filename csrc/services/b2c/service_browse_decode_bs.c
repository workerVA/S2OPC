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

#include "service_browse_decode_bs.h"

#include "sopc_types.h"

#include "util_b2c.h"

#include <assert.h>

/* Globals */
static OpcUa_BrowseRequest* request;

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void service_browse_decode_bs__INITIALISATION(void)
{
    request = NULL;
}

/*--------------------
   OPERATIONS Clause
  --------------------*/
/*@ requires \valid(req);
  @ requires \valid(service_browse_decode_bs__StatusCode_service);
  @
  @ behavior e_sc_ok:
  @        assumes 0 < req->NoOfNodesToBrowse && req->NoOfNodesToBrowse <= constants__k_n_BrowseResponse_max;
  @     requires \valid(request);
  @     assigns request;
  @     assigns *service_browse_decode_bs__StatusCode_service;
  @     ensures request == req;
  @     ensures *service_browse_decode_bs__StatusCode_service == constants__e_sc_ok;
  @
  @ behavior e_sc_bad_nothing_to_do:
  @        assumes 0 >= req->NoOfNodesToBrowse;
  @     assigns *service_browse_decode_bs__StatusCode_service;
  @     ensures *service_browse_decode_bs__StatusCode_service == constants__e_sc_bad_nothing_to_do;
  @
  @ behavior e_sc_bad_too_many_ops:
  @     assumes req->NoOfNodesToBrowse > constants__k_n_BrowseResponse_max;
  @     assigns *service_browse_decode_bs__StatusCode_service;
  @     ensures *service_browse_decode_bs__StatusCode_service == constants__e_sc_bad_too_many_ops;
  @
  @ disjoint behaviors;
  @ complete behaviors;
 */
static void s_decode_browse_request(OpcUa_BrowseRequest* req,
                                    constants__t_StatusCode_i* const service_browse_decode_bs__StatusCode_service)
{
    if (0 >= req->NoOfNodesToBrowse)
    {
        *service_browse_decode_bs__StatusCode_service = constants__e_sc_bad_nothing_to_do;
    }
    else if (req->NoOfNodesToBrowse > constants__k_n_BrowseResponse_max)
    {
        *service_browse_decode_bs__StatusCode_service = constants__e_sc_bad_too_many_ops;
    }
    else
    {
        /* TODO: req shall not be freed before request is null... */
        request = req;
        *service_browse_decode_bs__StatusCode_service = constants__e_sc_ok;
    }
}

#ifndef __FRAMAC__
void service_browse_decode_bs__decode_browse_request(
    const constants__t_msg_i service_browse_decode_bs__req_payload,
    constants__t_StatusCode_i* const service_browse_decode_bs__StatusCode_service)
{
    assert(*(SOPC_EncodeableType**) service_browse_decode_bs__req_payload == &OpcUa_BrowseRequest_EncodeableType);

    OpcUa_BrowseRequest* req = (OpcUa_BrowseRequest*) service_browse_decode_bs__req_payload;

    s_decode_browse_request(req, service_browse_decode_bs__StatusCode_service);
}
#endif // __FRAMAC__

/*@ requires \valid(request);
  @ assigns request;
  @ ensures request == \null;
 */

void service_browse_decode_bs__free_browse_request(void)
{
    /* TODO: don't free the request that you did not initialize */
    request = NULL;
}

/*@ requires \valid(service_browse_decode_bs__nb_req);
  @ requires \valid(request);
  @ assigns *service_browse_decode_bs__nb_req;
  @ ensures not_NULL_request: (\null != request) ==> *service_browse_decode_bs__nb_req == request->NoOfNodesToBrowse;
  @ ensures is_NULL_request: (\null == request) ==> *service_browse_decode_bs__nb_req == 0;
 */

void service_browse_decode_bs__get_nb_BrowseValue(t_entier4* const service_browse_decode_bs__nb_req)
{
    if (NULL != request)
        *service_browse_decode_bs__nb_req = request->NoOfNodesToBrowse;
    else
        *service_browse_decode_bs__nb_req = 0;
}

/*@ requires \valid(service_browse_decode_bs__p_nb_BrowseTargetMax);
  @ requires \valid(request);
  @ assigns *service_browse_decode_bs__p_nb_BrowseTargetMax;
  @ ensures 0 <= *service_browse_decode_bs__p_nb_BrowseTargetMax <= constants__k_n_BrowseTarget_max;
  @ ensures *service_browse_decode_bs__p_nb_BrowseTargetMax <= INT32_MAX;
  @ ensures request == \null ==> *service_browse_decode_bs__p_nb_BrowseTargetMax == 0;
  @ ensures (request != \null && request->RequestedMaxReferencesPerNode > 0 && request->RequestedMaxReferencesPerNode <
  INT32_MAX && request->RequestedMaxReferencesPerNode <= constants__k_n_BrowseTarget_max) ==>
  *service_browse_decode_bs__p_nb_BrowseTargetMax == (int32_t) request->RequestedMaxReferencesPerNode;
 */

void service_browse_decode_bs__get_nb_BrowseTargetMax(t_entier4* const service_browse_decode_bs__p_nb_BrowseTargetMax)
{
    if (NULL == request)
        *service_browse_decode_bs__p_nb_BrowseTargetMax = 0;
    else
    {
        if (request->RequestedMaxReferencesPerNode < INT32_MAX)
        {
            *service_browse_decode_bs__p_nb_BrowseTargetMax = (int32_t) request->RequestedMaxReferencesPerNode;
        }
        else
        {
            *service_browse_decode_bs__p_nb_BrowseTargetMax = INT32_MAX;
        }
        if (0 == *service_browse_decode_bs__p_nb_BrowseTargetMax ||
            *service_browse_decode_bs__p_nb_BrowseTargetMax > constants__k_n_BrowseTarget_max)
            *service_browse_decode_bs__p_nb_BrowseTargetMax = constants__k_n_BrowseTarget_max;
    }
}

/*@ requires \valid(service_browse_decode_bs__p_nid_view);
  @ requires \valid(request);
  @ assigns *service_browse_decode_bs__p_nid_view;
  @ ensures (request == \null || (request != \null && !((request->View.ViewId).IdentifierType !=
  SOPC_IdentifierType_Numeric || (request->View.ViewId).Data.Numeric != 0))) ==>
  *service_browse_decode_bs__p_nid_view == constants__c_NodeId_indet;
  @ ensures (request != \null && ((request->View.ViewId).IdentifierType != SOPC_IdentifierType_Numeric ||
  (request->View.ViewId).Data.Numeric != 0)) ==> *service_browse_decode_bs__p_nid_view == &(request->View.ViewId);
 */

extern void service_browse_decode_bs__get_BrowseView(constants__t_NodeId_i* const service_browse_decode_bs__p_nid_view)
{
    SOPC_NodeId* pVid = NULL;

    *service_browse_decode_bs__p_nid_view = constants__c_NodeId_indet;

    if (request != NULL)
    {
        pVid = &(request->View.ViewId);
        if (pVid->IdentifierType != SOPC_IdentifierType_Numeric || pVid->Data.Numeric != 0)
        {
            *service_browse_decode_bs__p_nid_view = pVid;
        }
    }
}

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

static bool s_BrowseDirection__C_to_B(OpcUa_BrowseDirection cdir, constants__t_BrowseDirection_i* bdir);

#ifndef __FRAMAC__
static bool s_BrowseDirection__C_to_B(OpcUa_BrowseDirection cdir, constants__t_BrowseDirection_i* bdir)
{
    return util_BrowseDirection__C_to_B(cdir, bdir);
}
#endif // __FRAMAC__

/*@ requires \valid(service_browse_decode_bs__p_isvalid);
  @ requires \valid(service_browse_decode_bs__p_NodeId);
  @ requires \valid(service_browse_decode_bs__p_dir);
  @ requires \valid(service_browse_decode_bs__p_isreftype);
  @ requires \valid(service_browse_decode_bs__p_reftype);
  @ requires \valid(service_browse_decode_bs__p_inc_subtype);
  @ requires \valid(request);
  @ requires \valid(request->NodesToBrowse);
  @ requires \valid(request->NodesToBrowse+(service_browse_decode_bs__p_bvi - 1));
  @ requires \separated(service_browse_decode_bs__p_isvalid, service_browse_decode_bs__p_NodeId,
  service_browse_decode_bs__p_dir, service_browse_decode_bs__p_isreftype, service_browse_decode_bs__p_reftype,
  service_browse_decode_bs__p_inc_subtype, request, request->NodesToBrowse+(service_browse_decode_bs__p_bvi - 1));
  @ assigns *service_browse_decode_bs__p_isvalid;
  @ assigns *service_browse_decode_bs__p_NodeId;
  @ assigns *service_browse_decode_bs__p_dir;
  @ assigns *service_browse_decode_bs__p_isreftype;
  @ assigns *service_browse_decode_bs__p_reftype;
  @ assigns *service_browse_decode_bs__p_inc_subtype;
  @
  @ behavior incorrect_request:
  @     assumes (\null == request || service_browse_decode_bs__p_bvi <= 0);
  @     ensures *service_browse_decode_bs__p_isvalid == false;
  @     ensures *service_browse_decode_bs__p_NodeId == constants__c_NodeId_indet;
  @     ensures *service_browse_decode_bs__p_dir == constants__e_bd_indet;
  @     ensures *service_browse_decode_bs__p_isreftype == false;
  @     ensures *service_browse_decode_bs__p_reftype == constants__c_NodeId_indet;
  @     ensures *service_browse_decode_bs__p_inc_subtype == false;
  @
  @ behavior correct_browse_request:
  @     assumes (\null != request && service_browse_decode_bs__p_bvi > 0);
  @     assumes (request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType !=
  SOPC_IdentifierType_Numeric || request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].ReferenceTypeId.Data.Numeric != 0);
  @     ensures *service_browse_decode_bs__p_isvalid == true;
  @     ensures *service_browse_decode_bs__p_NodeId == &request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].NodeId;
  @     ensures *service_browse_decode_bs__p_dir \in {constants__e_bd_indet, constants__e_bd_forward,
  constants__e_bd_inverse, constants__e_bd_both};
  @     ensures *service_browse_decode_bs__p_isreftype == true;
  @     ensures *service_browse_decode_bs__p_reftype == &request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].ReferenceTypeId;
  @     ensures *service_browse_decode_bs__p_inc_subtype ==
  (t_bool)(request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].IncludeSubtypes != 0);

  @
  @ behavior empty_browse_request:
  @     assumes (\null != request && service_browse_decode_bs__p_bvi > 0);
  @     assumes request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType ==
  SOPC_IdentifierType_Numeric && request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].ReferenceTypeId.Data.Numeric == 0;
  @     ensures *service_browse_decode_bs__p_isvalid == true;
  @     ensures *service_browse_decode_bs__p_NodeId == &request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].NodeId;
  @     ensures *service_browse_decode_bs__p_dir \in {constants__e_bd_indet, constants__e_bd_forward,
  constants__e_bd_inverse, constants__e_bd_both};
  @     ensures *service_browse_decode_bs__p_isreftype == false;
  @     ensures *service_browse_decode_bs__p_reftype == constants__c_NodeId_indet;
  @     ensures *service_browse_decode_bs__p_inc_subtype == false;

  @
  @ complete behaviors;
  @ disjoint behaviors;
*/

void service_browse_decode_bs__getall_BrowseValue(const constants__t_BrowseValue_i service_browse_decode_bs__p_bvi,
                                                  t_bool* const service_browse_decode_bs__p_isvalid,
                                                  constants__t_NodeId_i* const service_browse_decode_bs__p_NodeId,
                                                  constants__t_BrowseDirection_i* const service_browse_decode_bs__p_dir,
                                                  t_bool* const service_browse_decode_bs__p_isreftype,
                                                  constants__t_NodeId_i* const service_browse_decode_bs__p_reftype,
                                                  t_bool* const service_browse_decode_bs__p_inc_subtype)

{
    SOPC_NodeId* pNid = NULL;
    OpcUa_BrowseDescription* pBwseDesc = NULL;

    /* Default value for every output */
    *service_browse_decode_bs__p_isvalid = false;
    *service_browse_decode_bs__p_NodeId = constants__c_NodeId_indet;
    *service_browse_decode_bs__p_dir = constants__e_bd_indet;
    *service_browse_decode_bs__p_isreftype = false;
    *service_browse_decode_bs__p_reftype = constants__c_NodeId_indet;
    *service_browse_decode_bs__p_inc_subtype = false;

    if (NULL != request && service_browse_decode_bs__p_bvi > 0)
    /* && 0 < service_browse_decode_bs__p_bvi && service_browse_decode_bs__p_bvi <=
request->NoOfNodesToBrowse) These are already verified by PRE */
    {
        pBwseDesc = &request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1];
        *service_browse_decode_bs__p_NodeId = &pBwseDesc->NodeId;
        /* Invalid direction is tested by the B, so it's is not a reason to unset p_isvalid */
        s_BrowseDirection__C_to_B(pBwseDesc->BrowseDirection, service_browse_decode_bs__p_dir);

        /* TODO: Have a clearer definition of what a "not specified ReferenceType" is... */
        pNid = &request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId;

        /*@ requires \valid(pNid);
          @ requires \valid(pBwseDesc);
          @ requires \separated(service_browse_decode_bs__p_isreftype, service_browse_decode_bs__p_reftype,
          service_browse_decode_bs__p_inc_subtype);
          @ assigns *service_browse_decode_bs__p_isreftype;
          @ assigns *service_browse_decode_bs__p_reftype;
          @ assigns *service_browse_decode_bs__p_inc_subtype;
          @ ensures !(request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType ==
          SOPC_IdentifierType_Numeric && request->NodesToBrowse[service_browse_decode_bs__p_bvi -
          1].ReferenceTypeId.Data.Numeric == 0) ==> *service_browse_decode_bs__p_isreftype == true;
          @ ensures !(pNid->IdentifierType == SOPC_IdentifierType_Numeric && pNid->Data.Numeric == 0) ==>
          *service_browse_decode_bs__p_reftype == &request->NodesToBrowse[service_browse_decode_bs__p_bvi -
          1].ReferenceTypeId;
          @ ensures !(pNid->IdentifierType == SOPC_IdentifierType_Numeric && pNid->Data.Numeric == 0) ==>
          *service_browse_decode_bs__p_inc_subtype == (t_bool) (pBwseDesc->IncludeSubtypes != 0);
          @ ensures request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType ==
          SOPC_IdentifierType_Numeric && request->NodesToBrowse[service_browse_decode_bs__p_bvi -
          1].ReferenceTypeId.Data.Numeric == 0 ==> *service_browse_decode_bs__p_isreftype == false;
          @ ensures request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType ==
          SOPC_IdentifierType_Numeric && request->NodesToBrowse[service_browse_decode_bs__p_bvi -
          1].ReferenceTypeId.Data.Numeric == 0 ==> *service_browse_decode_bs__p_reftype == constants__c_NodeId_indet;
          @ ensures request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType ==
          SOPC_IdentifierType_Numeric && request->NodesToBrowse[service_browse_decode_bs__p_bvi -
          1].ReferenceTypeId.Data.Numeric == 0 ==> *service_browse_decode_bs__p_inc_subtype == false;
         */
        if (!(pNid->IdentifierType == SOPC_IdentifierType_Numeric && pNid->Data.Numeric == 0))
        {
            *service_browse_decode_bs__p_isreftype = true;
            //@ assert *service_browse_decode_bs__p_isreftype == true;
            *service_browse_decode_bs__p_reftype = pNid;
            *service_browse_decode_bs__p_inc_subtype = (t_bool) pBwseDesc->IncludeSubtypes;
            /*@ assert *service_browse_decode_bs__p_inc_subtype == (t_bool)
  (request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].IncludeSubtypes != 0);*/
        }

        *service_browse_decode_bs__p_isvalid = true;
    }
}

/*@ //requires \valid(service_browse_decode_bs__p_isvalid);
  @ //requires \valid(service_browse_decode_bs__p_NodeId);
  @ //requires \valid(service_browse_decode_bs__p_dir);
  @ requires \valid(service_browse_decode_bs__p_isreftype);
  @ requires \valid(service_browse_decode_bs__p_reftype);
  @ requires \valid(service_browse_decode_bs__p_inc_subtype);
  @ requires \valid(request);
  @ requires \valid(request->NodesToBrowse);
  @ requires \valid(request->NodesToBrowse+(service_browse_decode_bs__p_bvi - 1));
  @ requires \separated(service_browse_decode_bs__p_isreftype, service_browse_decode_bs__p_reftype,
  service_browse_decode_bs__p_inc_subtype, request, request->NodesToBrowse+(service_browse_decode_bs__p_bvi - 1));
  @ //assigns *service_browse_decode_bs__p_isvalid;
  @ //assigns *service_browse_decode_bs__p_NodeId;
  @ //assigns *service_browse_decode_bs__p_dir;
  @ assigns *service_browse_decode_bs__p_isreftype;
  @ assigns *service_browse_decode_bs__p_reftype;
  @ assigns *service_browse_decode_bs__p_inc_subtype;
  @
  @ behavior null:
  @ 	assumes !(NULL != request && service_browse_decode_bs__p_bvi > 0) ||
  (request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType ==
  SOPC_IdentifierType_Numeric && request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].ReferenceTypeId.Data.Numeric == 0);
  @ 	ensures *service_browse_decode_bs__p_isreftype == false;
  @ 	ensures *service_browse_decode_bs__p_reftype == constants__c_NodeId_indet;
  @ 	ensures *service_browse_decode_bs__p_inc_subtype == false;
  @
  @ behavior not_null:
  @ 	assumes NULL != request && service_browse_decode_bs__p_bvi > 0;
  @ 	assumes (request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType !=
  SOPC_IdentifierType_Numeric || request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].ReferenceTypeId.Data.Numeric != 0);
  @ 	ensures *service_browse_decode_bs__p_isreftype == true;
  @ 	ensures *service_browse_decode_bs__p_reftype == &request->NodesToBrowse[service_browse_decode_bs__p_bvi -
  1].ReferenceTypeId;
  @ 	ensures *service_browse_decode_bs__p_inc_subtype <==> (_Bool)
  request->NodesToBrowse[service_browse_decode_bs__p_bvi
  - 1].IncludeSubtypes;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/

void service_browse_decode_bs__getall_BrowseValue2(
    const constants__t_BrowseValue_i service_browse_decode_bs__p_bvi,
    // t_bool* const service_browse_decode_bs__p_isvalid,
    // constants__t_NodeId_i* const service_browse_decode_bs__p_NodeId,
    // constants__t_BrowseDirection_i* const service_browse_decode_bs__p_dir,
    t_bool* const service_browse_decode_bs__p_isreftype,
    constants__t_NodeId_i* const service_browse_decode_bs__p_reftype,
    t_bool* const service_browse_decode_bs__p_inc_subtype)
{
    SOPC_NodeId pNid;
    OpcUa_BrowseDescription pBwseDesc;

    /* Default value for every output */
    //*service_browse_decode_bs__p_isvalid = false;
    //*service_browse_decode_bs__p_NodeId = constants__c_NodeId_indet;
    //*service_browse_decode_bs__p_dir = constants__e_bd_indet;
    *service_browse_decode_bs__p_isreftype = false;
    *service_browse_decode_bs__p_reftype = constants__c_NodeId_indet;
    *service_browse_decode_bs__p_inc_subtype = false;

    if (NULL != request && service_browse_decode_bs__p_bvi > 0)
    /* && 0 < service_browse_decode_bs__p_bvi && service_browse_decode_bs__p_bvi <=
request->NoOfNodesToBrowse) These are already verified by PRE */
    {
        // pBwseDesc = request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1];
        //*service_browse_decode_bs__p_NodeId = &pBwseDesc->NodeId;
        /* Invalid direction is tested by the B, so it's is not a reason to unset p_isvalid */
        // s_BrowseDirection__C_to_B(pBwseDesc->BrowseDirection, service_browse_decode_bs__p_dir);

        /* TODO: Have a clearer definition of what a "not specified ReferenceType" is... */
        // pNid = request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId;
        if ((request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.IdentifierType !=
             SOPC_IdentifierType_Numeric) ||
            (request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId.Data.Numeric != 0))
        {
            *service_browse_decode_bs__p_isreftype = true;
            *service_browse_decode_bs__p_reftype =
                &request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].ReferenceTypeId;
            *service_browse_decode_bs__p_inc_subtype =
                request->NodesToBrowse[service_browse_decode_bs__p_bvi - 1].IncludeSubtypes;
        }

        //*service_browse_decode_bs__p_isvalid = true;
    }
}
