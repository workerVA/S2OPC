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
 * \file sopc_logger.h
 *
 *  \brief Specialized logger for the Toolkit
 */

#ifndef SOPC_LOGGER_H_
#define SOPC_LOGGER_H_

#include <stdbool.h>
#include <stdint.h>

#include "sopc_log_manager.h"

#ifdef __GNUC__
#define ATTR_FORMAT(archetype, string_index, first) __attribute__((format(archetype, string_index, first)))
#else
#define ATTR_FORMAT(archetype, string_index, first)
#endif

#define LOGGER_FUNC_FORMAT_ENUM ATTR_FORMAT(printf, 2, 3)
#define LOGGER_FUNC_FORMAT ATTR_FORMAT(printf, 1, 2)

/**
 * \brief log level enumeration
 */
typedef enum
{
    SOPC_LOG_LEVEL_ERROR = 0,
    SOPC_LOG_LEVEL_WARNING = 1,
    SOPC_LOG_LEVEL_INFO = 2,
    SOPC_LOG_LEVEL_DEBUG = 3
} SOPC_Log_Level;

/**
 * \brief enumerate to define log modules
 */
typedef enum SOPC_Log_Module
{
    SOPC_LOG_MODULE_COMMON,       /**< Common log module */
    SOPC_LOG_MODULE_CLIENTSERVER, /**< ClientServer log module */
    SOPC_LOG_MODULE_PUBSUB        /**< PubSub log module */
} SOPC_Log_Module;

/* TODO doc */
typedef void (*SOPC_Log_Initialize)(void);
typedef SOPC_Log_Instance* (*SOPC_Log_CreateInstance)(SOPC_Log_Configuration *log_configuration);
typedef SOPC_Log_Instance* (*SOPC_Log_CreateInstanceAssociation)(SOPC_Log_Instance* log_instance, const char* category);
typedef void (*SOPC_Log_VTrace)(SOPC_Log_Instance* pLogInst, SOPC_Log_Level level, const char* format, va_list args);
typedef void (*SOPC_Log_ClearInstance)(SOPC_Log_Instance** ppLogInst);
typedef void (*SOPC_Log_Clear)(void);

/**
 * \brief logger functions structure
 *
 * each logger should fill this structure with its functions
 */
typedef struct SOPC_Logger
{
    SOPC_Log_Initialize initialize;
    SOPC_Log_CreateInstance create_instance;
    SOPC_Log_CreateInstanceAssociation create_instance_assoc;
    SOPC_Log_VTrace vtrace;
    SOPC_Log_ClearInstance clear_instance;
    SOPC_Log_Clear clear;
} SOPC_Logger;

/*
 * \brief Initializes the logger and create the necessary log file(s)
 *
 * \param logDirPath   Absolute or relative path of the directory to be used for logs (shall exist and terminate with
 * directory separator)
 * \param maxBytes     A maximum amount of bytes by log file before opening a new file incrementing the integer suffix.
 * It is a best effort value (amount verified after each print).
 * \param maxFiles     A maximum number of files to be used, when reached the older log file is overwritten
 * (starting with *_00001.log)
 *
 * */
bool SOPC_Logger_Initialize(const char* logDirPath, uint32_t maxBytes, uint16_t maxFiles);

/*
 * \brief Defines the active log level for the given log instance (default: ERROR):
 * - ERROR: display only ERROR level
 * - WARNING: display ERROR + WARNING levels
 * - INFO: display ERROR + WARNING + INFO levels
 * - DEBUG: display ERROR + WARNING + INFO + DEBUG levels
 *
 * \param level     The level to be activated for the log instance
 */
void SOPC_Logger_SetTraceLogLevel(SOPC_Log_Level level);

/*
 * \brief Activates the console output for logged traces (same active level as log file)
 *
 * \param activate  Flag to activate / deactivate the console output
 */
void SOPC_Logger_SetConsoleOutput(bool activate);

/*
 * \brief Log a trace with the error level
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceError(SOPC_Log_Module logModule, const char* format, ...) LOGGER_FUNC_FORMAT_ENUM;

/*
 * \brief Log a trace with the warning level
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceWarning(SOPC_Log_Module logModule, const char* format, ...) LOGGER_FUNC_FORMAT_ENUM;

/*
 * \brief Log a trace with the info level
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceInfo(SOPC_Log_Module logModule, const char* format, ...) LOGGER_FUNC_FORMAT_ENUM;

/*
 * \brief Log a trace with the debug level
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceDebug(SOPC_Log_Module logModule, const char* format, ...) LOGGER_FUNC_FORMAT_ENUM;

/*
 * \brief Log a trace for the security audit log
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceSecurityAudit(const char* format, ...) LOGGER_FUNC_FORMAT;

/*
 * \brief Log a warning trace for the security audit log
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceSecurityAuditWarning(const char* format, ...) LOGGER_FUNC_FORMAT;

/*
 * \brief Log a trace for the OPC UA audit log
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceOpcUaAudit(const char* format, ...) LOGGER_FUNC_FORMAT;

/*
 * \brief Log a warning trace for the OPC UA audit log
 *
 * \param format    String specifying how subsequent arguments are converted for output
 */
void SOPC_Logger_TraceOpcUaAuditWarning(const char* format, ...) LOGGER_FUNC_FORMAT;

/*
 * \brief Clears the logger and close the current log files
 * */
void SOPC_Logger_Clear(void);

#endif /* SOPC_LOGGER_H_ */
