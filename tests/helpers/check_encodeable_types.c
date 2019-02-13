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
    // Endianness init
    SOPC_Helper_EndiannessCfg_Initialize();
}

/**
 * TimeZoneDataType unitary test
 * Test of Initialize, Decode and Encode functions
 */
START_TEST(test_time_zone_data_type)
{
    OpcUa_TimeZoneDataType* time_zone_data_type = malloc(sizeof *time_zone_data_type);
    SOPC_ReturnStatus return_status = SOPC_STATUS_OK;

    // Test trame creation (with cursor position reset)
    uint8_t trame[] = {0xFF, 0xFF, 0x1};
    size_t trame_size = sizeof trame;

    // Buffer initialization
    SOPC_Buffer* buffer_input = SOPC_Buffer_Create((uint32_t) trame_size);
    SOPC_Buffer* buffer_output = SOPC_Buffer_Create((uint32_t) trame_size);

    return_status = SOPC_Buffer_Write(buffer_input, trame, (uint32_t) trame_size);
    ck_assert(return_status == SOPC_STATUS_OK);
    return_status = SOPC_Buffer_SetPosition(buffer_input, 0);
    ck_assert(return_status == SOPC_STATUS_OK);

    // Initialization
    OpcUa_TimeZoneDataType_EncodeableType.Initialize(time_zone_data_type);

    // Decode
    return_status = OpcUa_TimeZoneDataType_EncodeableType.Decode(time_zone_data_type, buffer_input);
    ck_assert(return_status == SOPC_STATUS_OK);

    // Check content of encodeable type
    ck_assert(time_zone_data_type->Offset == -1);                   // 0xFF FF -> -1
    ck_assert(time_zone_data_type->DaylightSavingInOffset == true); // 0x1 -> true

    // Encode
    return_status = OpcUa_TimeZoneDataType_EncodeableType.Encode(time_zone_data_type, buffer_output);
    ck_assert(return_status == SOPC_STATUS_OK);

    // Check buffers
    ck_assert_mem_eq(buffer_input->data, buffer_output->data, trame_size);

    // Clear
    OpcUa_TimeZoneDataType_EncodeableType.Clear(time_zone_data_type);

}
END_TEST

/**
 * AggregateFilterResult unitary test
 * Test of Initialize, decode and encode functions 
 */
START_TEST(test_aggregate_filter_result)
{
    OpcUa_AggregateFilterResult* aggregate_filter_result = calloc(1, sizeof *aggregate_filter_result);
    SOPC_ReturnStatus return_status = SOPC_STATUS_OK;

    // Test trame creation (with cursor position reset)
    uint8_t trame[] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // 8B SOPC_Date_Time
                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // 8B double
                       0x01, 0x01, 0x2A, 0x3A, 0x01}; // 5B AggregateConfiguration
    size_t trame_size = sizeof trame;

    // Buffer initialization
    SOPC_Buffer* buffer_input = SOPC_Buffer_Create((uint32_t) trame_size);
    SOPC_Buffer* buffer_output = SOPC_Buffer_Create((uint32_t) trame_size);

    return_status = SOPC_Buffer_Write(buffer_input, trame, (uint32_t) trame_size);
    ck_assert(return_status == SOPC_STATUS_OK);
    return_status = SOPC_Buffer_SetPosition(buffer_input, 0);
    ck_assert(return_status == SOPC_STATUS_OK);

    // Initialization
    OpcUa_AggregateFilterResult_EncodeableType.Initialize(aggregate_filter_result);

    // Decode
    return_status = OpcUa_AggregateFilterResult_EncodeableType.Decode(aggregate_filter_result, buffer_input);
    ck_assert(return_status == SOPC_STATUS_OK);

    // Check content of encodeable type
    ck_assert_int_eq(aggregate_filter_result->RevisedStartTime, -1);
    ck_assert_double_eq(aggregate_filter_result->RevisedProcessingInterval, 0);

    // Check content of nested encodeable type
    OpcUa_AggregateConfiguration* wanted_aggregate_configuration = calloc(1, sizeof *wanted_aggregate_configuration);
    OpcUa_AggregateConfiguration_EncodeableType.Initialize(wanted_aggregate_configuration);
    wanted_aggregate_configuration->UseServerCapabilitiesDefaults = true;
    wanted_aggregate_configuration->TreatUncertainAsBad = true;
    wanted_aggregate_configuration->PercentDataBad = 0x2A;
    wanted_aggregate_configuration->PercentDataGood = 0x3A;
    wanted_aggregate_configuration->UseSlopedExtrapolation = true;

    ck_assert_mem_eq(wanted_aggregate_configuration,
                     &(aggregate_filter_result->RevisedAggregateConfiguration),
                     sizeof *wanted_aggregate_configuration); // nested encodeable type

    OpcUa_AggregateConfiguration_EncodeableType.Clear(wanted_aggregate_configuration);

    // Encode
    return_status = OpcUa_AggregateFilterResult_EncodeableType.Encode(aggregate_filter_result, buffer_output);
    ck_assert(return_status == SOPC_STATUS_OK);

    // Check buffers
    ck_assert_mem_eq(buffer_input->data, buffer_output->data, trame_size);

    // Clear
    OpcUa_AggregateFilterResult_EncodeableType.Clear(aggregate_filter_result);
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
    suite_add_tcase(s, tc_encodeable_types);

    return s;
}
