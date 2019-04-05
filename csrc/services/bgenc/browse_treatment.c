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

/******************************************************************************

 File Name            : browse_treatment.c

 Date                 : 05/04/2019 14:46:18

 C Translator Version : tradc Java V1.0 (14/03/2012)

******************************************************************************/

/*------------------------
   Exported Declarations
  ------------------------*/
#include "browse_treatment.h"

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void browse_treatment__INITIALISATION(void) {
}

/*--------------------
   OPERATIONS Clause
  --------------------*/
void browse_treatment__min_max_nb_result_refs(
   const t_entier4 browse_treatment__p_maxTargetRef,
   const t_entier4 browse_treatment__p_nb_target,
   t_entier4 * const browse_treatment__p_maxResultRefs) {
   if (0 < browse_treatment__p_maxTargetRef) {
      *browse_treatment__p_maxResultRefs = browse_treatment__p_maxTargetRef;
   }
   else {
      *browse_treatment__p_maxResultRefs = browse_treatment__p_nb_target;
   }
}

void browse_treatment__fill_browse_result(
   const t_entier4 browse_treatment__p_startIndex,
   const t_entier4 browse_treatment__p_max_nb_results,
   const constants__t_NodeId_i browse_treatment__p_browseView,
   const constants__t_Node_i browse_treatment__p_src_node,
   const constants__t_BrowseDirection_i browse_treatment__p_browseDirection,
   const t_bool browse_treatment__p_refType_defined,
   const constants__t_NodeId_i browse_treatment__p_referenceType,
   const t_bool browse_treatment__p_includeSubtypes,
   constants_statuscodes_bs__t_StatusCode_i * const browse_treatment__p_serviceStatusCode,
   t_bool * const browse_treatment__p_toContinue,
   t_entier4 * const browse_treatment__p_nextIndex) {
   *browse_treatment__p_serviceStatusCode = constants_statuscodes_bs__c_StatusCode_indet;
   *browse_treatment__p_toContinue = false;
   *browse_treatment__p_nextIndex = 0;
}

void browse_treatment__set_browse_value_context(
   const constants__t_session_i browse_treatment__p_session,
   const t_entier4 browse_treatment__p_maxTargetRef,
   const constants__t_NodeId_i browse_treatment__p_browseView,
   const constants__t_NodeId_i browse_treatment__p_nodeId,
   const constants__t_BrowseDirection_i browse_treatment__p_browseDirection,
   const constants__t_NodeId_i browse_treatment__p_referenceType,
   const t_bool browse_treatment__p_includeSubtypes) {
   browse_treatment_context__setall_browse_value_context(1,
      browse_treatment__p_session,
      browse_treatment__p_maxTargetRef,
      browse_treatment__p_browseView,
      browse_treatment__p_nodeId,
      browse_treatment__p_browseDirection,
      browse_treatment__p_referenceType,
      browse_treatment__p_includeSubtypes);
}

void browse_treatment__set_browse_value_context_from_continuation_point(
   const constants__t_session_i browse_treatment__p_session,
   const constants__t_ContinuationPoint_i browse_treatment__p_continuationPoint,
   constants_statuscodes_bs__t_StatusCode_i * const browse_treatment__p_service_StatusCode) {
   *browse_treatment__p_service_StatusCode = constants_statuscodes_bs__e_sc_bad_continuation_point_invalid;
}

void browse_treatment__compute_browse_result(
   constants_statuscodes_bs__t_StatusCode_i * const browse_treatment__p_serviceStatusCode,
   constants__t_ContinuationPoint_i * const browse_treatment__p_continuationPoint,
   t_entier4 * const browse_treatment__p_nbReferences) {
   {
      t_entier4 browse_treatment__l_startIndex;
      constants__t_session_i browse_treatment__l_session;
      t_entier4 browse_treatment__l_maxTargetRef;
      constants__t_NodeId_i browse_treatment__l_browseView;
      constants__t_NodeId_i browse_treatment__l_nodeId;
      constants__t_BrowseDirection_i browse_treatment__l_browseDirection;
      t_bool browse_treatment__l_refType_defined;
      constants__t_NodeId_i browse_treatment__l_referenceType;
      t_bool browse_treatment__l_includeSubtypes;
      t_bool browse_treatment__l_is_src_node_valid;
      t_entier4 browse_treatment__l_nb_target;
      constants__t_Node_i browse_treatment__l_src_node;
      t_bool browse_treatment__l_alloc_bres;
      t_entier4 browse_treatment__l_max_nb_results;
      t_bool browse_treatment__l_toContinue;
      t_entier4 browse_treatment__l_nextIndex;
      t_bool browse_treatment__l_cp_bres;
      
      *browse_treatment__p_continuationPoint = constants__c_ContinuationPoint_indet;
      *browse_treatment__p_nbReferences = 0;
      browse_treatment_context__getall_browse_value_context(&browse_treatment__l_startIndex,
         &browse_treatment__l_session,
         &browse_treatment__l_maxTargetRef,
         &browse_treatment__l_browseView,
         &browse_treatment__l_nodeId,
         &browse_treatment__l_browseDirection,
         &browse_treatment__l_refType_defined,
         &browse_treatment__l_referenceType,
         &browse_treatment__l_includeSubtypes);
      browse_treatment_1__getall_SourceNode_NbRef(browse_treatment__l_nodeId,
         &browse_treatment__l_is_src_node_valid,
         &browse_treatment__l_nb_target,
         &browse_treatment__l_src_node);
      if (browse_treatment__l_is_src_node_valid == true) {
         browse_treatment__min_max_nb_result_refs(browse_treatment__l_maxTargetRef,
            browse_treatment__l_nb_target,
            &browse_treatment__l_max_nb_results);
         browse_treatment_result_bs__alloc_browse_result(browse_treatment__l_max_nb_results,
            &browse_treatment__l_alloc_bres);
         if (browse_treatment__l_alloc_bres == true) {
            browse_treatment__fill_browse_result(browse_treatment__l_startIndex,
               browse_treatment__l_max_nb_results,
               browse_treatment__l_browseView,
               browse_treatment__l_src_node,
               browse_treatment__l_browseDirection,
               browse_treatment__l_refType_defined,
               browse_treatment__l_referenceType,
               browse_treatment__l_includeSubtypes,
               browse_treatment__p_serviceStatusCode,
               &browse_treatment__l_toContinue,
               &browse_treatment__l_nextIndex);
            if (browse_treatment__l_toContinue == true) {
               browse_treatment_continuation_points__create_continuation_point(browse_treatment__l_session,
                  browse_treatment__l_nextIndex,
                  browse_treatment__l_maxTargetRef,
                  browse_treatment__l_browseView,
                  browse_treatment__l_nodeId,
                  browse_treatment__l_browseDirection,
                  browse_treatment__l_referenceType,
                  browse_treatment__l_includeSubtypes,
                  &browse_treatment__l_cp_bres,
                  browse_treatment__p_continuationPoint);
               if (browse_treatment__l_cp_bres == false) {
                  *browse_treatment__p_serviceStatusCode = constants_statuscodes_bs__e_sc_bad_no_continuation_points;
               }
            }
         }
         else {
            *browse_treatment__p_serviceStatusCode = constants_statuscodes_bs__e_sc_bad_out_of_memory;
         }
      }
      else {
         *browse_treatment__p_serviceStatusCode = constants_statuscodes_bs__e_sc_bad_node_id_unknown;
      }
   }
}

