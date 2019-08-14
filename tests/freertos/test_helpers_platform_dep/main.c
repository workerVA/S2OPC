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

#include <stdio.h>

#include "lwip/opt.h"
#include "lwip/tcpip.h"

#include "board.h"
#include "clock_config.h"
#include "ethernetif.h"
#include "netif/ethernet.h"
#include "peripherals.h"
#include "pin_mux.h"

#include "FreeRTOS.h"
#include "MIMXRT1064.h"
#include "queue.h"
#include "task.h"
#include "timers.h"

#include "fsl_debug_console.h"
#include "fsl_device_registers.h"
#include "fsl_gpio.h"
#include "fsl_iomuxc.h"
#include "fsl_qtmr.h"

#include "sopc_mutexes.h"
#include "sopc_threads.h"
#include "sopc_udp_sockets.h"

#include "FreeRTOSTest.h"

#include "ksdk_mbedtls_config.h"
#include "p_ethernet_if.h"
#include "p_generic_socket_srv.h"
#include "p_time.h"

// Global variables

Condition gHandleConditionVariable;

#if (configUSE_BOGOMIPS == 1)
extern float external_bogomips(void);
float gPerformanceValue = 0.0;
#endif

#if (configUSE_ANALYZER == 1)
#include "p_analyzer.h"
tLogSrvWks* gAnalyzerSrv;
static void cbAnalyzerCreation(void** pAnalyzerContext, tLogClientWks* pClt)
{
    *pAnalyzerContext = CreateAnalyzer(5000 / P_LOG_CLT_RX_PERIOD);
}
static void cbAnalyzerDestruction(void** pAnalyzerContext, tLogClientWks* pClt)
{
    DestroyAnalyzer((tAnalyzerWks**) pAnalyzerContext);
}
static eResultDecoder cbAnalyzerExecution(void* pAnalyzerContext,
                                          tLogClientWks* pClt,
                                          const uint8_t* pBufferIn,
                                          uint16_t dataSize,
                                          uint8_t* pBufferOut,
                                          uint16_t* pOutSize,
                                          uint16_t maxSizeBufferOut)
{
    // Don't modify dataSize output, echo simulation
    uint16_t wIter = 0;
    eAnalyzerStatus status;
    tAnalyzerMsg* pMsg;
    uint16_t byteSent;

    for (wIter = 0; wIter < dataSize; wIter++)
    {
        status = ExecuteAnalyzer(pAnalyzerContext, pBufferIn[wIter]);
        if (status == ANALYZER_STATUS_READY)
        {
            pMsg = GetReadyMessage(pAnalyzerContext);
            if (pMsg != NULL)
            {
                printf("Tag recu = %d\r\n", pMsg->tag);
                printf("Length recue = %d\r\n", pMsg->length);
                printf("Data recue : ");
                for (int i = 0; i < pMsg->length; i++)
                {
                    printf("%2X ", pMsg->data[i]);
                }
                printf("\r\n");

                byteSent = 0;

                P_LOG_CLIENT_SendResponse(pClt, ((uint8_t*) pMsg), pMsg->length + 3, &byteSent);
                if (byteSent != pMsg->length + 3)
                {
                    return E_DECODER_RESULT_ERROR_NOK;
                }
            }
        }
    }

    *pOutSize = 0;
    return E_DECODER_RESULT_OK;
}

static eResultEncoder cbEncoderCallback(void* pAnalyzerContext,
                                        const uint8_t* pBufferIn,
                                        uint16_t dataSize,
                                        uint8_t* pBufferOut,
                                        uint16_t* pOutSize,
                                        uint16_t maxSizeBufferOut)
{
    tAnalyzerMsg* msg = NULL;

    if (PLT_MAX_FRAME_SIZE > maxSizeBufferOut)
    {
        *pOutSize = 0;
        return E_ENCODER_RESULT_ERROR_NOK;
    }

    msg = (tAnalyzerMsg*) pBufferIn;
    *pOutSize = BuildFrame(msg->tag, msg->length, msg->data, maxSizeBufferOut, pBufferOut);

    if (*pOutSize > 0)
    {
        memset(pBufferOut, 0, maxSizeBufferOut);
        memcpy(pBufferOut, pBufferIn, *pOutSize);
    }
    return E_ENCODER_RESULT_OK;
}

#endif

int main(void)
{
    // Configuration of MPU. I and D cache are disabled.
    BOARD_ConfigMPU();
    // Initialization of GPIO
    BOARD_InitPins();
    // Initialization  of clocks
    BOARD_BootClockRUN();
    // Initialization of SDK debug console
    BOARD_InitDebugConsole();

    // Initialization of MCU ENET driver
    // Initialization of MCU Timer 3 used by FreeRTOS
    // to generate 10KHz signal and measure cpu load per thread
    BOARD_InitBootPeripherals();

#if (configUSE_BOGOMIPS == 1)
    gPerformanceValue = external_bogomips();
#endif

    // Network interface initialization (IP @...)
    // P_ETHERNET_IF_IsReady shall be called
    // to verify if interface is ready, else
    // lwip socket api crash.
    P_ETHERNET_IF_Initialize();

    // Init tick to UTC time (build date)
    P_TIME_SetInitialDateToBuildTime();

    // Attach S2OPC Mutexes mechanism to mbedtls.
    mbedtls_threading_initialize();

    // used by FreeRTOS thread validation.
    Condition_Init(&gHandleConditionVariable);

    // FreeRTOS thread validation. This test shall be running ad vitam ethernam.
    // FREE_RTOS_TEST_API_S2OPC_THREAD(&gHandleConditionVariable);

    // Toolkit server application
    // FREE_RTOS_TEST_S2OPC_SERVER(&gHandleConditionVariable);

    // Toolkit client application
    // FREE_RTOS_TEST_S2OPC_CLIENT(&gHandleConditionVariable);

    // Unit test copy from tests sources. CHECK_TIME
    // FREE_RTOS_TEST_S2OPC_TIME(&gHandleConditionVariable);

    // Unit test copy from tests sources. CHECK_THREAD and MUTEX and COND VAR
    // FREE_RTOS_TEST_S2OPC_CHECK_THREAD(&gHandleConditionVariable);

    // FREE_RTOS_TEST_S2OPC_UDP_SOCKET_API(&gHandleConditionVariable);

    FREE_RTOS_TEST_S2OPC_PUBSUB(NULL);

    // FREE_RTOS_TEST_S2OPC_USECASE_PUBSUB_SYNCHRO(NULL);

#if (configUSE_TRACE_ANALYZER == 1)
    vTraceEnable(TRC_INIT);
#endif

#if (configUSE_ANALYZER == 1)

    gAnalyzerSrv = P_LOG_SRV_CreateAndStart(61, 4023, 1, 0, 0,                                                    //
                                            cbAnalyzerCreation, cbAnalyzerDestruction, cbAnalyzerExecution, NULL, //
                                            NULL, NULL, cbEncoderCallback, NULL,                                  //
                                            NULL);                                                                //
#endif
    vTaskStartScheduler();

    for (;;)
        ;
}
