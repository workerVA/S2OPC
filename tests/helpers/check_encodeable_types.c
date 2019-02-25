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
 * \brief Entry point for encodeable types tests. Tests use libcheck.
 *
 * If you want to debug the exe, you should define env var CK_FORK=no
 * http://check.sourceforge.net/doc/check_html/check_4.html#No-Fork-Mode
 */

#include <check.h>
#include <stdlib.h>

#include "check_helpers.h"

#include "sopc_encodeable.h"
#include "sopc_helper_endianness_cfg.h"
#include "sopc_types.h"

static void setup(void)
{
    SOPC_Helper_EndiannessCfg_Initialize();
}

static void ck_assert_ok(SOPC_ReturnStatus status)
{
    ck_assert(SOPC_STATUS_OK == status);
}

#define ck_assert_encodeable_type(obj, type) ck_assert_ptr_eq((obj)->encodeableType, &type##_EncodeableType)

/******************************************************************************
 * Generic checker for encodeable types
 * Test of Initialize, Decode and Encode functions
 * The type and the checker function are received as parameters, as well as the
 * buffer to be decoded.
 ******************************************************************************/
static void check_encodeable_type(SOPC_EncodeableType* enc_type,
                                  void (*encodeable_type_checker)(void*),
                                  uint8_t* frame,
                                  uint32_t frame_size)
{
    // Allocation
    void* obj = NULL;
    SOPC_Buffer* input = NULL;
    SOPC_Buffer* output = NULL;

    // Buffer initialization
    input = SOPC_Buffer_Create(frame_size);
    output = SOPC_Buffer_Create(frame_size);

    ck_assert_ok(SOPC_Buffer_Write(input, frame, frame_size));
    ck_assert_ok(SOPC_Buffer_SetPosition(input, 0));

    // Initialization
    SOPC_Encodeable_Create(enc_type, &obj);
    ck_assert_ptr_nonnull(obj);

    // Decode
    ck_assert_ok(enc_type->Decode(obj, input));

    // Check object content
    encodeable_type_checker(obj);

    // Encode
    ck_assert_ok(enc_type->Encode(obj, output));

    // Check buffers
    ck_assert_uint_eq(output->position, frame_size);
    ck_assert_mem_eq(input->data, output->data, frame_size);

    // Clear all objects
    SOPC_Encodeable_Delete(enc_type, &obj);
    SOPC_Buffer_Delete(input);
    SOPC_Buffer_Delete(output);
}

/******************************************************************************
 * TimeZoneDataType unitary test
 ******************************************************************************/

static void time_zone_data_type_checker(void* encodeable_type_object)
{
    OpcUa_TimeZoneDataType* obj = encodeable_type_object;

    // Check content
    ck_assert_encodeable_type(obj, OpcUa_TimeZoneDataType);
    ck_assert(obj->Offset == -1);
    ck_assert(obj->DaylightSavingInOffset == true);
}

START_TEST(test_time_zone_data_type)
{
    // Test frame creation
    uint8_t frame[] = {0xFF, 0xFF,  // Offset == -1
                       0x01};       // DaylightSavingInOffset == true

    check_encodeable_type(&OpcUa_TimeZoneDataType_EncodeableType,
                          time_zone_data_type_checker,
                          frame,
                          (uint32_t) sizeof frame);
}
END_TEST

/******************************************************************************
 * AggregateFilterResult unitary test
 ******************************************************************************/

static void aggregate_filter_result_checker(void* encodeable_type_object)
{
    OpcUa_AggregateFilterResult* obj = encodeable_type_object;
    OpcUa_AggregateConfiguration* nested_obj = NULL;

    ck_assert_encodeable_type(obj, OpcUa_AggregateFilterResult);
    ck_assert_int_eq(obj->RevisedStartTime, -1);
    ck_assert_double_eq(obj->RevisedProcessingInterval, 0);

    nested_obj = &obj->RevisedAggregateConfiguration;
    ck_assert_encodeable_type(nested_obj, OpcUa_AggregateConfiguration);
    ck_assert_int_eq(nested_obj->UseServerCapabilitiesDefaults, true);
    ck_assert_int_eq(nested_obj->TreatUncertainAsBad, true);
    ck_assert_uint_eq(nested_obj->PercentDataBad, 0x2A);
    ck_assert_uint_eq(nested_obj->PercentDataGood, 0x3A);
    ck_assert_int_eq(nested_obj->UseSlopedExtrapolation, true);
}

START_TEST(test_aggregate_filter_result)
{
    // Test frame creation (with cursor position reset)
    uint8_t frame[] = {// 8B RevisedStartTime == -1
                       0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                       // 8B double == 0
                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 

                       // 5B AggregateConfiguration
                       0x01,  // UseServerCapabilitiesDefaults == true
                       0x01,  // TreatUncertainAsBad           == true
                       0x2A,  // PercentDataBad                == 42
                       0x3A,  // PercentDataGood               == 58
                       0x01}; // UseSlopedExtrapolation        == true                 

    check_encodeable_type(&OpcUa_AggregateFilterResult_EncodeableType,
                          aggregate_filter_result_checker,
                          frame,
                          (uint32_t) sizeof frame);
}
END_TEST

/******************************************************************************
 * BrowsePath unitary test
 ******************************************************************************/

static void browse_path_checker(void* encodeable_type_object)
{
    OpcUa_BrowsePath* obj = encodeable_type_object;
    OpcUa_RelativePath* path;
    OpcUa_RelativePathElement* elem;

    ck_assert_encodeable_type(obj, OpcUa_BrowsePath);
    ck_assert_int_eq(obj->StartingNode.IdentifierType, SOPC_IdentifierType_Numeric);
    ck_assert_int_eq(obj->StartingNode.Namespace, 0x02);
    ck_assert_uint_eq(obj->StartingNode.Data.Numeric, 0x0403);

    path = &obj->RelativePath;
    ck_assert_encodeable_type(path, OpcUa_RelativePath);
    ck_assert_int_eq(path->NoOfElements, 2);
    ck_assert_ptr_nonnull(path->Elements);

    elem = &path->Elements[0];
    ck_assert_encodeable_type(elem, OpcUa_RelativePathElement);
    ck_assert_int_eq(elem->ReferenceTypeId.IdentifierType, SOPC_IdentifierType_Numeric);
    ck_assert_int_eq(elem->ReferenceTypeId.Namespace, 0x05);
    ck_assert_uint_eq(elem->ReferenceTypeId.Data.Numeric, 0x0706);
    ck_assert_int_eq(elem->IsInverse, false);
    ck_assert_int_eq(elem->IncludeSubtypes, true);
    ck_assert_uint_eq(elem->TargetName.NamespaceIndex, 0x0908);
    ck_assert_int_eq(elem->TargetName.Name.Length, -1);
    ck_assert_int_eq(elem->TargetName.Name.DoNotClear, false);
    ck_assert_ptr_null(elem->TargetName.Name.Data);

    elem = &path->Elements[1];
    ck_assert_encodeable_type(elem, OpcUa_RelativePathElement);
    ck_assert_int_eq(elem->ReferenceTypeId.IdentifierType, SOPC_IdentifierType_Numeric);
    ck_assert_int_eq(elem->ReferenceTypeId.Namespace, 0x0A);
    ck_assert_uint_eq(elem->ReferenceTypeId.Data.Numeric, 0x0C0B);
    ck_assert_int_eq(elem->IsInverse, true);
    ck_assert_int_eq(elem->IncludeSubtypes, false);
    ck_assert_uint_eq(elem->TargetName.NamespaceIndex, 0x0E0D);
    ck_assert_int_eq(elem->TargetName.Name.Length, 4);
    ck_assert_int_eq(elem->TargetName.Name.DoNotClear, false);
    ck_assert_pstr_eq((char*) elem->TargetName.Name.Data, "mugu");
}

START_TEST(test_browse_path)
{
    // Test frame creation
    uint8_t frame[] = {
                       // BrowsePath->StartingNodeId
                       0x01, // Four byte encoding of NodeId
                       0x02, // Namespace == 2
                       0x03, 0x04, // Identifier == 0x0403

                       // BrowsePath->RelativePath
                       0x02, 0x00, 0x00, 0x00, // NoOfElements == 2

                       // BrowsePath->RelativePath.Element[0]
                       // ReferenceTypeId
                       0x01, // Four byte encoding of NodeId
                       0x05, // Namespace == 5
                       0x06, 0x07, // Identifier == 0x0706

                       0x00, // IsInverse == false
                       0x01, // IncludeSubtypes == true

                       // TargetName
                       0x08, 0x09, // NamespaceIndex == 0x0908
                       0xff, 0xff, 0xff, 0xff, // Name (null)

                       // BrowsePath->RelativePath.Element[1]
                       // ReferenceTypeId
                       0x01, // Four byte encoding of NodeId
                       0x0A, // Namespace == 0x0A
                       0x0B, 0x0C, // Identifier == 0x0C0B

                       0x01, // IsInverse == true
                       0x00, // IncludeSubtypes == false

                       // TargetName
                       0x0D, 0x0E, // NamespaceIndex = 0
                       0x04, 0x00, 0x00, 0x00, // Name length
                       0x6D, 0x75, 0x67, 0x75  // Name Data == "mugu"
    };

    check_encodeable_type(&OpcUa_BrowsePath_EncodeableType,
                          browse_path_checker,
                          frame,
                          (uint32_t) sizeof frame);
}
END_TEST

/******************************************************************************
 * DeleteSubscriptionsRequest unitary test
 ******************************************************************************/

static void delete_subscriptions_request_checker(void* encodeable_type_object)
{
    OpcUa_DeleteSubscriptionsRequest* obj = encodeable_type_object;

    ck_assert_encodeable_type(obj, OpcUa_DeleteSubscriptionsRequest);
    ck_assert_int_eq(obj->NoOfSubscriptionIds, 2);
    ck_assert_uint_eq(obj->SubscriptionIds[0], 5);
    ck_assert_uint_eq(obj->SubscriptionIds[1], 10);
}

START_TEST(test_delete_subscriptions_request)
{
    // Test frame creation (with cursor position reset)
    uint8_t frame[] = {
        0x02, 0x00, 0x00, 0x00, // NoOfSubscriptionIds == 2
        0x05, 0x00, 0x00, 0x00, // SubscriptionsIds[0] == 5
        0x0A, 0x00, 0x00, 0x00  // SubscriptionsIds[1] == 10
                       };                 

    check_encodeable_type(&OpcUa_DeleteSubscriptionsRequest_EncodeableType,
                          delete_subscriptions_request_checker,
                          frame,
                          (uint32_t) sizeof frame);
}
END_TEST

Suite* tests_make_suite_encodeable_types(void)
{
    Suite* s;
    TCase* tc_encodeable_types;

    s = suite_create("Tests for encodeable types");

    tc_encodeable_types = tcase_create("Encodeable_Types");

    tcase_add_checked_fixture(tc_encodeable_types, setup, NULL);
    tcase_add_test(tc_encodeable_types, test_time_zone_data_type);
    tcase_add_test(tc_encodeable_types, test_aggregate_filter_result);
    tcase_add_test(tc_encodeable_types, test_browse_path);
    tcase_add_test(tc_encodeable_types, test_delete_subscriptions_request);
    suite_add_tcase(s, tc_encodeable_types);

    return s;
}