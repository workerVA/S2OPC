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

/**
 * \file sopc_log_manager.h
 *
 *  \brief A log manager providing circular logging, multiple logging categories and levels with thread-safe accesses.
 */

#ifndef SOPC_LOGGER_NO_LOG_H
#define SOPC_LOGGER_NO_LOG_H

#include "sopc_logger.h"

/**
 * \brief get the logger structure
 */
SOPC_Logger SOPC_Logger_NoLog_Get(void);

#endif /* SOPC_LOGGER_NO_LOG_H */
