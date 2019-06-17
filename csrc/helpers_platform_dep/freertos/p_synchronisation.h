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

#ifndef P_SYNCHRONISATION_H
#define P_SYNCHRONISATION_H

#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

#include "p_utils.h"

/*****Private condition variable api*****/

#define MAX_WAITERS (MAX_P_UTILS_LIST)

#define JOINTURE_SIGNAL (0x80000000)
#define JOINTURE_CLEAR_SIGNAL (0x40000000)
#define APP_DEFAULT_SIGNAL (0x20000000)
#define APP_CLEARING_SIGNAL (0x10000000)

typedef struct T_CONDITION_VARIABLE tConditionVariable;
typedef tConditionVariable* hCondVar;

typedef enum T_CONDITION_VARIABLE_RESULT
{
    E_COND_VAR_RESULT_OK,
    E_COND_VAR_RESULT_ERROR_NOK,
    E_COND_VAR_RESULT_ERROR_OUT_OF_MEM,
    E_COND_VAR_RESULT_ERROR_TIMEOUT,
    E_COND_VAR_RESULT_ERROR_INCORRECT_PARAMETERS,
    E_COND_VAR_RESULT_ERROR_MAX_WAITERS,
    E_COND_VAR_RESULT_ERROR_NO_WAITERS,
    E_COND_VAR_RESULT_ERROR_NOT_INITIALIZED,
    E_COND_VAR_RESULT_ERROR_ALREADY_INITIALIZED
} eConditionVariableResult;

hCondVar* P_SYNCHRO_CreateConditionVariable(void);

void P_SYNCHRO_DestroyConditionVariable(hCondVar** pv);

eConditionVariableResult P_SYNCHRO_InitConditionVariable(hCondVar* pv, uint16_t wMaxWaiters);

eConditionVariableResult P_SYNCHRO_ClearConditionVariable(hCondVar* pv);

eConditionVariableResult P_SYNCHRO_SignalAllConditionVariable(hCondVar* pv);
eConditionVariableResult P_SYNCHRO_SignalConditionVariable(hCondVar* pv);

eConditionVariableResult P_SYNCHRO_UnlockAndWaitForConditionVariable(hCondVar* pv,
                                                                     QueueHandle_t* pMutex,
                                                                     uint32_t uwSignal,
                                                                     uint32_t uwClearSignal,
                                                                     uint32_t uwTimeOutMs);

/*****Public s2opc condition variable and mutex api*****/

typedef hCondVar Condition;
typedef QueueHandle_t Mutex;

#endif
