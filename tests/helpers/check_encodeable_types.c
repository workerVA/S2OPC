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
 * \brief Entry point for threads tests. Tests use libcheck.
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

/**
 * TimeZoneDataType unitary test
 * Test of Initialize, Decode and Encode functions
 */
START_TEST(test_time_zone_data_type)
{
    // Endianness init
    SOPC_Helper_EndiannessCfg_Initialize();

    OpcUa_TimeZoneDataType* t_time_zone_date_type = (OpcUa_TimeZoneDataType*) malloc(sizeof(OpcUa_TimeZoneDataType));
    SOPC_ReturnStatus t_status = SOPC_STATUS_INVALID_PARAMETERS;

    // Buffer initialization
    SOPC_Buffer* t_buffer_input = SOPC_Buffer_Create(3);
    SOPC_Buffer* t_buffer_output = SOPC_Buffer_Create(3);

    // Test trame creation (with cursor position reset)
    uint8_t t_trame[] = {0xFF, 0xFF, 0x1};
    size_t trame_size = (int) sizeof(t_trame);

    t_status = SOPC_Buffer_Write(t_buffer_input, t_trame, (uint32_t) trame_size);
    ck_assert(t_status == SOPC_STATUS_OK);
    t_status = SOPC_Buffer_SetPosition(t_buffer_input, 0);
    ck_assert(t_status == SOPC_STATUS_OK);

    // Initialization
    OpcUa_TimeZoneDataType_EncodeableType.Initialize(t_time_zone_date_type);

    // Decode
    t_status = OpcUa_TimeZoneDataType_EncodeableType.Decode(t_time_zone_date_type, t_buffer_input);
    ck_assert(t_status == SOPC_STATUS_OK);

    // Check content of encodeable type
    ck_assert(t_time_zone_date_type->Offset == -1);                   // 0xFF FF -> -1
    ck_assert(t_time_zone_date_type->DaylightSavingInOffset == true); // 0x1 -> true

    // Encode
    t_status = OpcUa_TimeZoneDataType_EncodeableType.Encode(t_time_zone_date_type, t_buffer_output);
    ck_assert(t_status == SOPC_STATUS_OK);

    // Check buffers
    ck_assert(memcmp(t_buffer_input->data, t_buffer_output->data, trame_size) == 0);

    // Clear
    OpcUa_TimeZoneDataType_EncodeableType.Clear(t_time_zone_date_type);
}
END_TEST

Suite* tests_make_suite_encodeable_types(void)
{
    Suite* s;
    TCase* tc_time_zone_data_type;

    s = suite_create("Tests for encodeable types");

    tc_time_zone_data_type = tcase_create("TimeZoneDataType");
    tcase_add_test(tc_time_zone_data_type, test_time_zone_data_type);
    suite_add_tcase(s, tc_time_zone_data_type);

    return s;
}
