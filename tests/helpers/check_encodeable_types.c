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

/******************************************************************************
 * Generic checker for encodeable types
 * Test of Initialize, Decode and Encode functions
 * The type and the checker function are received as parameters, as well as the
 * buffer to be decoded.
 ******************************************************************************/
static void check_encodeable_type(SOPC_EncodeableType* encodeable_type,
                                  void (*encodeable_type_checker)(void*),
                                  uint8_t* frame,
                                  uint32_t frame_size)
{
    // Allocation
    void* encodeable_object = calloc(1, encodeable_type->AllocationSize);
    ck_assert_ptr_nonnull(encodeable_object);

    // Buffer initialization
    SOPC_Buffer* buffer_input = SOPC_Buffer_Create(frame_size);
    SOPC_Buffer* buffer_output = SOPC_Buffer_Create(frame_size);

    ck_assert(SOPC_Buffer_Write(buffer_input, frame, frame_size) == SOPC_STATUS_OK);
    ck_assert(SOPC_Buffer_SetPosition(buffer_input, 0) == SOPC_STATUS_OK);

    // Initialization
    encodeable_type->Initialize(encodeable_object);

    // Decode
    ck_assert(encodeable_type->Decode(encodeable_object, buffer_input) == SOPC_STATUS_OK);

    // Check object content
    encodeable_type_checker(encodeable_object);

    // Encode
    ck_assert(encodeable_type->Encode(encodeable_object, buffer_output) == SOPC_STATUS_OK);

    // Check buffers
    ck_assert_int_eq(buffer_output->position, frame_size);
    ck_assert_mem_eq(buffer_input->data, buffer_output->data, frame_size);

    // Clear all objects
    encodeable_type->Clear(encodeable_object);
    SOPC_Buffer_Delete(buffer_input);
    SOPC_Buffer_Delete(buffer_output);
}

/******************************************************************************
 * TimeZoneDataType unitary test
 ******************************************************************************/

static void time_zone_data_type_checker(void* encodeable_type_object)
{
    OpcUa_TimeZoneDataType* time_zone_data_type_object = encodeable_type_object;

    ck_assert(time_zone_data_type_object->encodeableType == &OpcUa_TimeZoneDataType_EncodeableType);
    ck_assert(time_zone_data_type_object->Offset == -1);
    ck_assert(time_zone_data_type_object->DaylightSavingInOffset == true);
}

START_TEST(test_time_zone_data_type)
{
    // Test frame creation
    uint8_t frame[] = {0xFF, 0xFF, 0x1};
    uint32_t frame_size = (uint32_t) sizeof frame;

    check_encodeable_type(&OpcUa_TimeZoneDataType_EncodeableType, time_zone_data_type_checker, frame, frame_size);
}
END_TEST

/******************************************************************************
 * AggregateFilterResult unitary test
 ******************************************************************************/

static void aggregate_filter_result_checker(void* encodeable_type_object)
{
    OpcUa_AggregateFilterResult* aggregate_filter_result_object = encodeable_type_object;

    // Check content
    ck_assert_int_eq(aggregate_filter_result_object->RevisedStartTime, -1);
    ck_assert_double_eq(aggregate_filter_result_object->RevisedProcessingInterval, 0);

    // Check content of nested encodeable type
    ck_assert_int_eq(aggregate_filter_result_object->RevisedAggregateConfiguration.UseServerCapabilitiesDefaults, true);
    ck_assert_int_eq(aggregate_filter_result_object->RevisedAggregateConfiguration.TreatUncertainAsBad, true);
    ck_assert_int_eq(aggregate_filter_result_object->RevisedAggregateConfiguration.PercentDataBad, 0x2A);
    ck_assert_int_eq(aggregate_filter_result_object->RevisedAggregateConfiguration.PercentDataGood, 0x3A);
    ck_assert_int_eq(aggregate_filter_result_object->RevisedAggregateConfiguration.UseSlopedExtrapolation, true);
}

START_TEST(test_aggregate_filter_result)
{
    // Test frame creation (with cursor position reset)
    uint8_t frame[] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, // 8B SOPC_Date_Time
                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // 8B double
                       0x01, 0x01, 0x2A, 0x3A, 0x01};                  // 5B AggregateConfiguration

    check_encodeable_type(&OpcUa_AggregateFilterResult_EncodeableType, aggregate_filter_result_checker, frame,
                          (uint32_t) sizeof frame);
}
END_TEST

/******************************************************************************
 * BrowsePath unitary test
 ******************************************************************************/

static void browse_path_checker(void* encodeable_type_object)
{
    OpcUa_BrowsePath* browse_path_object = encodeable_type_object;

    // Check content
    ck_assert_int_eq(browse_path_object->StartingNode.IdentifierType, 0);
    ck_assert_int_eq(browse_path_object->StartingNode.Namespace, 4);
    ck_assert_int_eq(browse_path_object->StartingNode.Data.Numeric, 3);

    // Check content of nested encodeable type
    ck_assert_int_eq(browse_path_object->RelativePath.NoOfElements, 2);
    ck_assert_ptr_nonnull(browse_path_object->RelativePath.Elements);

    // Check content of Element of nested encodeable type)
    ck_assert_int_eq(browse_path_object->RelativePath.Elements[0].ReferenceTypeId.Data.Numeric, 3);
    ck_assert_int_eq(browse_path_object->RelativePath.Elements[0].IncludeSubtypes, true);
    ck_assert_int_eq(browse_path_object->RelativePath.Elements[1].ReferenceTypeId.Data.Numeric, 171);
    ck_assert_int_eq(browse_path_object->RelativePath.Elements[1].IsInverse, true);
}

START_TEST(test_browse_path)
{
    // Test frame creation
    uint8_t frame[] = {0x01, 0x04, 0x03, 0x00, // BrowsePath->StartingNodeId
                       0x02, 0x00, 0x00, 0x00, // BrowsePath->RelativePath->NoOfElements
                       0x01, 0x04, 0x03, 0x00, // BrowsePath->RelativePath First element node id
                       0x00, 0x01, 0x00, 0x00, // IncludeSubtypes true
                       0xff, 0xff, 0xff, 0xff,
                       0x01, 0x05, 0xAB, 0x00, // BrowsePath->RelativePath Second element node id
                       0x01, 0x00, 0x00, 0x00, // IsInverse true
                       0xff, 0xff, 0xff, 0xff};

    check_encodeable_type(&OpcUa_BrowsePath_EncodeableType, browse_path_checker, frame, (uint32_t) sizeof frame);
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
    suite_add_tcase(s, tc_encodeable_types);

    return s;
}
