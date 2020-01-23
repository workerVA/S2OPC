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

#ifndef FUZZ_MGR__RECEIVE_MSG_BUFFER_SERVER
#define FUZZ_MGR__RECEIVE_MSG_BUFFER_SERVER

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

#include "fuzz_main.h"

// def! setup
SOPC_ReturnStatus Setup_serv(void);    // Server initialization
SOPC_ReturnStatus SOPC_EpConfig_serv();

// !endef

typedef enum
{
    AS_LOADER_EMBEDDED,
} AddressSpaceLoader;

extern SOPC_AddressSpace* address_space;
extern t_CerKey ck_serv;
extern uint32_t epConfigIdx;
extern SOPC_UserAuthentication_Manager* authenticationManager;
extern SOPC_UserAuthorization_Manager* authorizationManager;

#endif // FUZZ_MGR__RECEIVE_MSG_BUFFER_SERVER
