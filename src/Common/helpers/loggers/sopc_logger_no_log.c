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

/*
 * \brief Initializes the logger manager: generate unique file name prefix for execution
 */
static void SOPC_Logger_NoLog_Initialize(void)
{
    return;
}

/*
 * \brief Creates a new log file and log instance and prints the starting timestamp
 *
 * \return             The log instance to be used to add traces
 */
static SOPC_Log_Instance* SOPC_Logger_NoLog_CreateInstance(SOPC_Log_Configuration* log_configuration)
{
    (void) (log_configuration);
    return NULL;
}

/*
 * \brief Creates a new log instance using the same log file than existing log instance and prints the starting
 * timestamp. It provides the way to have several categories with different levels of log in the same log file.
 *
 * \param pLogInst  An existing log instance used to print in the same log file
 * \param category  Category for the new log instance in the log file (should be unique in log file)
 *
 * \return          The log instance to be used to add traces
 */
static SOPC_Log_Instance* SOPC_Logger_NoLog_CreateInstanceAssociation(SOPC_Log_Instance* pLogInst, const char* category)
{
    (void) (pLogInst);
    (void) (category);

    return NULL;
}

/*
 * \brief Logs a trace with the given level
 *
 * \param pLogInst  An existing log instance already started
 * \param level     The log level corresponding to the given trace
 * \param format    String specifying how subsequent arguments are converted for output
 * \param args      Arguments used by the string specifying the output
 */
static void SOPC_Logger_NoLog_VTrace(SOPC_Log_Instance* pLogInst, SOPC_Log_Level level, const char* format, va_list args)
{
    (void) (pLogInst);
    (void) (level);
    (void) (format);
    (void) (args);
}

/*
 * \brief Stops allowing to log traces in the given log instance. Log file is closed when last log instance is stopped.
 *
 * \param ppLogInst  An existing log instance already started. Pointer set to NULL after call.
 */
static void SOPC_Logger_NoLog_ClearInstance(SOPC_Log_Instance** ppLogInst)
{
    (void) (ppLogInst);
}

/*
 * \brief Clears the logger manager: clear unique file name prefix for execution
 * */
static void SOPC_Logger_NoLog_Clear(void)
{
    return;
}

SOPC_Logger SOPC_Logger_NoLog_Get(void)
{
    SOPC_Logger logger = {
        .initialize = SOPC_Logger_NoLog_Initialize;
        .create_instance = SOPC_Logger_NoLog_CreateInstance;
        .create_instance_assoc = SOPC_Logger_NoLog_CreateInstanceAssociation;
        .vtrace = SOPC_Logger_NoLog_VTrace;
        .clear_instance = SOPC_Logger_NoLog_ClearInstance;
        .clear = SOPC_Logger_NoLog_Clear;
    };
    return logger:
}
