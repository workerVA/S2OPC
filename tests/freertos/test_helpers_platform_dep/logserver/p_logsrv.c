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

#include "p_logsrv.h"

// Log server status
typedef enum E_LOG_SERVER_STATUS
{
    E_LOG_SERVER_CLOSING,
    E_LOG_SERVER_BINDING,
    E_LOG_SERVER_ONLINE
} eLogServerStatus;

// Log server workspace
typedef struct T_LOG_SERVER_WORKSPACE
{
    // Server status
    eLogServerStatus status; // Server status

    // Socket identifier
    int32_t socketTCP; // Server socket
    int32_t socketUDP; // Temporary socket to send hello message.

    // Server configuration
    uint16_t maxClient; // Max clients
    uint16_t port;      // Server port
    uint16_t portHello; // UDP port destination for hello message

    uint32_t timeoutClientS; // Timeout in S for client connexion keep alive
    uint32_t periodeHello;   // Periode of hello message
    uint32_t timerHello;     // Timer of hello message

    // Client list
    tUtilsList clientList; // Client list connected to the server

    // Broadcaster channem
    tChannel broadCastChannel; // Broadcast channel, used to send a same message
    // to all connected client. Use by log API

    // Server tasks
    TaskHandle_t handleTask;      // Handle connexion monitoring and broadcast message
    QueueHandle_t quitRequest;    // Signal quit request
    QueueHandle_t joinServerTask; // Signal join server task

    // Tx buffer for "broadcast" (send same message to all client)
    // and announcement message
    uint8_t bufferSRV_TX[P_LOG_FIFO_ELT_MAX_SIZE];

    // Optional common callback associated to clients

    ptrFct_AnalyzerContextCreation cbClientAnalyzerContextCreation;       // Context creation callback
    ptrFct_AnalyzerContextDestruction cbClientAnalyzerContextDestruction; // Context destruction callback.
    ptrFct_AnalyzerCallback cbClientAnalyzer;                             // Input Frame decoder
    ptrFct_AnalyzerPeriodic cbClientAnalyzerPeriodic;                     // Input frame periodic tick timeout.

    ptrFct_EncoderContextCreation cbClientEncoderContextCreation;       // Output frame context creation
    ptrFct_EncoderContextDestruction cbClientEncoderContextDestruction; // Output frame encoder context destruction
    ptrFct_EncoderCallback cbClientEncoder;                             // Output frame encoder.
    ptrFct_EncoderPeriodicCallback cbClientEncoderPeriodic;             // Output frame encoder periodic timeout tick.

    ptrFct_EncoderTransmitHelloCallback cbEncoderTransmitHello; // Hello callback.

} tLogSrvWks;

// Status definition for server client
typedef enum E_LOG_CLIENT_STATUS
{
    E_LOG_CLIENT_DISCONNECTED,
    E_LOG_CLIENT_CONNECTED
} eLogClientStatus;

// Server Client workspace
typedef struct T_LOG_CLIENT_WORKSPACE
{
    eLogClientStatus status; // Client status
    int32_t socket;          // Socket

    uint32_t timeoutActivite;     // Cpt period
    uint32_t trigTimeoutActivite; // Nb period of non RX activity

    uint8_t bActiviteTx; // Flag activity for debug
    uint8_t bActiviteRx;

    uint8_t bufferTX[P_LOG_FIFO_ELT_MAX_SIZE];       // Buffer TX
    uint8_t bufferRX[P_LOG_FIFO_ELT_MAX_SIZE];       // Buffer RX from monitoring
    uint8_t bufferANALYZER[P_LOG_FIFO_ELT_MAX_SIZE]; // Buffer RX from encoder task

    tLogSrvWks* pServer; // Handle server

    TaskHandle_t handleTaskMonitor; // Handle task monitor + rx
    TaskHandle_t handleTaskTx;      // Handle task encoder + tx
    TaskHandle_t handleTaskRx;      // Handle task decoder + action

    QueueHandle_t joinClientTaskMonitor; // Join monitor + rx
    QueueHandle_t joinClientTaskTx;      // Join encoder + tx
    QueueHandle_t joinClientTaskRx;      // Join decoder + action

    QueueHandle_t quitRequestTaskMonitor; // Quit request signal monitor + rx
    QueueHandle_t quitRequestTaskTx;      // Quit request signal encoder + tx
    QueueHandle_t quitRequestTaskRx;      // Quit request signal decoder + action

    tChannel channelInput;  // Channel between monitor + rx and decoder + action
    tChannel channelOutput; // Channel between server and encoder + tx for broadcast
    // Safely shared with

    // See server workspace description

    ptrFct_AnalyzerContextCreation cbAnalyzerContextCreation;
    ptrFct_AnalyzerContextDestruction cbAnalyzerContextDestruction;
    ptrFct_AnalyzerCallback cbAnalyzer;
    ptrFct_AnalyzerPeriodic cbAnalyzerPeriodic;

    ptrFct_EncoderContextCreation cbEncoderContextCreation;
    ptrFct_EncoderContextDestruction cbEncoderContextDestruction;
    ptrFct_EncoderCallback cbEncoder;
    ptrFct_EncoderPeriodicCallback cbEncoderPeriodic;

    void* ptrAnalyzerContext; // Optional context for analyzer
    void* ptrEncoderContext;  // Optional context for encoder

} tLogClientWks;

// Static Callbacks declarations

static void cbTaskSocketClientEncodeAndTx(void* pParameters); // Callback encode + tx
static void cbTaskSocketClientDecodeAndDo(void* pParameters); // Callback decode + action / response
static void cbTaskSocketClientRxAndMon(void* pParameters);    // Callback monitore + rx
static void cbTaskSocketServerMonAndLog(void* pParameters);   // Server connexion callback + announce + "broadcast"

// Static client workspace creation and destruction

static tLogClientWks* ClientCreateThenStart(
    int32_t socket,    // socket
    tLogSrvWks* pServ, // attached server
    uint32_t timeoutS, // timeout connexion

    ptrFct_AnalyzerContextCreation cbAnalyzerContextCreationCallback,       // analyzer context creation
    ptrFct_AnalyzerContextDestruction cbAnalyzerContextDestructionCallback, // analyzer context destruction
    ptrFct_AnalyzerCallback cbAnalyzerCallback,                             // analyzer
    ptrFct_AnalyzerPeriodic cbAnalyzerTimeOutCallback,                      // analyzer tick timeout

    ptrFct_EncoderContextCreation cbClientSenderContextCreation,       // encoder context creation
    ptrFct_EncoderContextDestruction cbClientSenderContextDestruction, // encoder context destruction
    ptrFct_EncoderCallback cbClientSenderCallback,                     // encoder
    ptrFct_EncoderPeriodicCallback cbClientSenderTimeoutCallback);     // tick timeout

static void ClientStopThenDestroy(tLogClientWks** p);

// Callbacks definitions

// Callback of encoding and sending frame
static void cbTaskSocketClientEncodeAndTx(void* pParameters)
{
    tLogClientWks* pClt = (tLogClientWks*) pParameters;
    eChannelResult resChannel = E_CHANNEL_RESULT_OK;
    TickType_t xTicksToWait = 0;
    TimeOut_t xTimeOut = {0, 0};
    uint16_t nbBytes = 0;
    uint16_t iIter = 0;
    int16_t byteSent = 0; // Used by lwip, -1 if error on socket

    if (NULL != pClt)
    {
        pClt->bActiviteTx = 0;

        // Encoder context creation if callback exists
        if (NULL != pClt->cbEncoderContextCreation)
        {
            pClt->cbEncoderContextCreation(&pClt->ptrEncoderContext);
        }

        // Task of analyzer (decoder) is created. Give join signal in case of error.
        xSemaphoreGive(pClt->joinClientTaskRx);

        if (xTaskCreate(cbTaskSocketClientDecodeAndDo,  //
                        "logCltRx",                     //
                        P_LOG_CLT_RX_CALLBACK_STACK,    //
                        pClt,                           //
                        configMAX_PRIORITIES - 1,       //
                        &pClt->handleTaskRx) == pdPASS) //
        {
            DEBUG_incrementCpt();

            // Task created, join signal taken
            xSemaphoreTake(pClt->joinClientTaskRx, 0);

            vTaskSetTimeOutState(&xTimeOut); //---Period initilization
            xTicksToWait = pdMS_TO_TICKS(P_LOG_CLT_TX_PERIOD);

            // Encoder loop on client status and quit request
            while ((E_LOG_CLIENT_CONNECTED == pClt->status) && (pdFAIL == xSemaphoreTake(pClt->quitRequestTaskTx, 0)))
            {
                // Wait on reception of bytes to encode
                memset(pClt->bufferTX, 0, sizeof(pClt->bufferTX));

                resChannel = P_CHANNEL_Receive(&pClt->channelOutput,      //
                                               NULL,                      //
                                               &pClt->bufferTX[0],        //
                                               &nbBytes,                  //
                                               sizeof(pClt->bufferTX),    //
                                               xTicksToWait,              //
                                               E_CHANNEL_RD_MODE_NORMAL); //

                // In case of event (flush or rx)
                if (E_CHANNEL_RESULT_ERROR_TMO != resChannel)
                {
                    pClt->bActiviteTx = 1;
                    // If encoding callback, buffer TX can be modified and nbBytes also just after send.
                    // In case of error of encoderCallback, client disconnected.
                    if (pClt->cbEncoder != NULL)
                    {
                        if (E_ENCODER_RESULT_OK !=
                            pClt->cbEncoder(pClt->ptrEncoderContext, pClt->bufferTX, &nbBytes, sizeof(pClt->bufferTX)))
                        {
                            pClt->status = E_LOG_CLIENT_DISCONNECTED;
                        }
                    }

                    // Check if nbBytes to send < size of buffer TX because not guaranteed after modification by
                    // callback. In case of lwip error, client disconnected
                    if ((nbBytes <= sizeof(pClt->bufferTX)) && (nbBytes > 0))
                    {
                        byteSent = 0;
                        for (iIter = 0; (iIter < nbBytes) && (byteSent >= 0); iIter += (uint16_t) byteSent)
                        {
                            byteSent = lwip_send(pClt->socket, pClt->bufferTX + iIter, nbBytes - iIter, 0);
                            if (byteSent < 0)
                            {
                                pClt->status = E_LOG_CLIENT_DISCONNECTED;
                            }
                        }
                    }

                    xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait); //---Period reajust
                }
                else
                {
                    vTaskSetTimeOutState(&xTimeOut); //---Period reajust
                    xTicksToWait = pdMS_TO_TICKS(P_LOG_CLT_TX_PERIOD);

                    //-------------------------Periodic zone--------------------------------

                    // If encoder tick timeout exist, if it returns an error, client is disconnected
                    if (pClt->cbEncoderPeriodic != NULL)
                    {
                        if (pClt->cbEncoderPeriodic(pClt->ptrAnalyzerContext) != E_ENCODER_RESULT_OK)
                        {
                            pClt->status = E_LOG_CLIENT_DISCONNECTED;
                        }
                    }

                    pClt->bActiviteTx = 0;

                    xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait); //---Period reajust
                }

            } // End of encoder loop

            // Set status to disconnected, flush channel on wich analyzer task is maybe waiting
            // then set qui signal, and wait join signal from analyzer task.
            pClt->bActiviteTx = 0;
            pClt->status = E_LOG_CLIENT_DISCONNECTED;
            P_CHANNEL_Flush(&pClt->channelInput);
            xSemaphoreGive(pClt->quitRequestTaskRx);
            xSemaphoreTake(pClt->joinClientTaskRx, portMAX_DELAY);
        }
        else
        {
            // Task analyzer can't be created
            pClt->status = E_LOG_CLIENT_DISCONNECTED;
        }

        // Destroy lwip socket workspace
        if (pClt->socket != -1)
        {
            lwip_shutdown(pClt->socket, SHUT_RDWR);
            lwip_close(pClt->socket);
            DEBUG_decrementCpt();
            pClt->socket = -1;
        }

        // Destroy encoder workspace
        if (pClt->cbEncoderContextDestruction != NULL)
        {
            pClt->cbEncoderContextDestruction(&pClt->ptrEncoderContext);
            pClt->ptrEncoderContext = NULL;
        }

        // Send signal to monitor task that this task is well terminated
        xSemaphoreGive(pClt->joinClientTaskTx);
    }
    DEBUG_decrementCpt();
    vTaskDelete(NULL);
}

// Callback decoding, execute action if necessary and send response
static void cbTaskSocketClientDecodeAndDo(void* pParameters)
{
    tLogClientWks* pClt = (tLogClientWks*) pParameters;

    eChannelResult resChannel = E_CHANNEL_RESULT_NOK;
    eChannelResult resChannelSent = E_CHANNEL_RESULT_OK;
    TickType_t xTicksToWait = 0;
    TimeOut_t xTimeOut = {0, 0};
    uint16_t nbBytes = 0;
    uint16_t wIterSent = 0;
    uint16_t nbBytesSent = 0;

    if (NULL != pClt)
    {
        pClt->bActiviteRx = 0;

        // Analyzer context creation. If exist, can save context handle to ptrAnalyzerContext
        if (NULL != pClt->cbAnalyzerContextCreation)
        {
            pClt->cbAnalyzerContextCreation(&pClt->ptrAnalyzerContext, pClt);
        }

        vTaskSetTimeOutState(&xTimeOut); //--Period initialization
        xTicksToWait = pdMS_TO_TICKS(P_LOG_CLT_RX_PERIOD);

        // Analyzer loop, quit if client status = DISCONNECTED or if quit request received
        while ((E_LOG_CLIENT_CONNECTED == pClt->status) && (pdFAIL == xSemaphoreTake(pClt->quitRequestTaskRx, 0)))
        {
            memset(pClt->bufferANALYZER, 0, sizeof(pClt->bufferANALYZER));
            // Check if bytes received
            resChannel = P_CHANNEL_Receive(&pClt->channelInput,          //
                                           NULL,                         //
                                           &pClt->bufferANALYZER[0],     //
                                           &nbBytes,                     //
                                           sizeof(pClt->bufferANALYZER), //
                                           xTicksToWait,                 //
                                           E_CHANNEL_RD_MODE_NORMAL);    //

            // If not a timeout, analyze bytes and do action
            // send response via channel out is possible, max frame size in parameters.
            // In case of ERROR returned by callback, client disconnected
            if (E_CHANNEL_RESULT_ERROR_TMO != resChannel)
            {
                pClt->bActiviteRx = 1;
                if (NULL != pClt->cbAnalyzer)
                {
                    if (pClt->cbAnalyzer(pClt->ptrAnalyzerContext,   //
                                         pClt, pClt->bufferANALYZER, //
                                         &nbBytes,                   //
                                         sizeof(pClt->bufferANALYZER)) != E_DECODER_RESULT_OK)
                    {
                        pClt->status = E_LOG_CLIENT_DISCONNECTED;
                    }
                    else
                    {
                        if ((nbBytes > 0) && (nbBytes <= sizeof(pClt->bufferANALYZER)))
                        {
                            resChannelSent = E_CHANNEL_RESULT_OK;
                            for (wIterSent = 0;                                                    //
                                 (wIterSent < nbBytes) && (resChannelSent == E_CHANNEL_RESULT_OK); //
                                 wIterSent += nbBytesSent)                                         //
                            {
                                resChannelSent = P_CHANNEL_Send(&pClt->channelOutput,             //
                                                                &pClt->bufferANALYZER[wIterSent], //
                                                                nbBytes - wIterSent,              //
                                                                &nbBytesSent,                     //
                                                                E_CHANNEL_WR_MODE_NORMAL);        //

                                if (resChannelSent == E_CHANNEL_RESULT_ERROR_FULL)
                                {
                                    P_CHANNEL_Flush(&pClt->channelOutput);
                                }
                            }
                        }
                    }
                    // Raz nb bytes to send, set by callback return
                    nbBytes = 0;
                }
                xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait); //---Period reajust
            }
            else
            {
                vTaskSetTimeOutState(&xTimeOut); //---Period reinit
                xTicksToWait = pdMS_TO_TICKS(P_LOG_CLT_RX_PERIOD);

                //-------------------------Periodic zone--------------------------------

                pClt->bActiviteRx = 0;
                // Timeout if nothing to analyze. If timeout tick callback return error, so client disconnected
                if (NULL != pClt->cbAnalyzerPeriodic)
                {
                    // Raz output buffer
                    nbBytes = 0;
                    memset(pClt->bufferANALYZER, 0, sizeof(pClt->bufferANALYZER));

                    // Periodic callback called
                    if (pClt->cbAnalyzerPeriodic(pClt->ptrAnalyzerContext,                             //
                                                 pClt,                                                 //
                                                 pClt->bufferANALYZER,                                 //
                                                 &nbBytes,                                             //
                                                 sizeof(pClt->bufferANALYZER)) != E_DECODER_RESULT_OK) //
                    {
                        pClt->status = E_LOG_CLIENT_DISCONNECTED;
                    }
                    else
                    {
                        // If no error and output, send data to encoder. Check limit before.
                        if ((nbBytes > 0) && (nbBytes <= sizeof(pClt->bufferANALYZER)))
                        {
                            resChannelSent = E_CHANNEL_RESULT_OK;
                            for (wIterSent = 0;                                                    //
                                 (wIterSent < nbBytes) && (resChannelSent == E_CHANNEL_RESULT_OK); //
                                 wIterSent += nbBytesSent)                                         //
                            {
                                resChannelSent = P_CHANNEL_Send(&pClt->channelOutput,             //
                                                                &pClt->bufferANALYZER[wIterSent], //
                                                                nbBytes - wIterSent,              //
                                                                &nbBytesSent,                     //
                                                                E_CHANNEL_WR_MODE_NORMAL);        //

                                if (resChannelSent == E_CHANNEL_RESULT_ERROR_FULL)
                                {
                                    P_CHANNEL_Flush(&pClt->channelOutput);
                                }
                            }
                        }
                    }
                    // Raz nb bytes to send, set by callback return.
                    nbBytes = 0;
                }

                xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait); //---Period reajust
            }
        }

        pClt->bActiviteRx = 0;

        // Analyzer context destruction callback
        if (pClt->cbAnalyzerContextDestruction != NULL)
        {
            pClt->cbAnalyzerContextDestruction(&pClt->ptrAnalyzerContext, pClt);
            pClt->ptrAnalyzerContext = NULL;
        }

        // Send signal to Encoder task which is waiting the end of this task.
        xSemaphoreGive(pClt->joinClientTaskRx);
    }
    DEBUG_decrementCpt();
    vTaskDelete(NULL);
}

// Callback of client socket monitoring and reception of data,
// which are sent to analyzer task.
static void cbTaskSocketClientRxAndMon(void* pParameters)
{
    tLogClientWks* p = (tLogClientWks*) pParameters;
    TickType_t xTimeToWait = 0;
    TimeOut_t xTimeOut = {0, 0};
    int32_t nbBytesReceived = 0;
    eChannelResult resChannelSent = E_CHANNEL_RESULT_OK;
    uint16_t nbBytesSent = 0;
    uint16_t wIterSent = 0;
    struct timeval timeout;
    fd_set rdfs;

    vTaskSetTimeOutState(&xTimeOut);
    timeout.tv_sec = 0;
    timeout.tv_usec = 1000 * P_LOG_CLT_MONITOR_PERIOD;
    xTimeToWait = pdMS_TO_TICKS(P_LOG_CLT_MONITOR_PERIOD);

    if (NULL != p)
    {
        // Creation task of encoding before continue
        // Give signal join in the case of task creation failure
        xSemaphoreGive(p->joinClientTaskTx);

        if (xTaskCreate(cbTaskSocketClientEncodeAndTx, //
                        "logCltTx",                    //
                        P_LOG_CLT_TX_CALLBACK_STACK,   //
                        p,                             //
                        configMAX_PRIORITIES - 1,      //
                        &p->handleTaskTx) == pdPASS)   //
        {
            DEBUG_incrementCpt();
            // Reset join signal, task well created
            xSemaphoreTake(p->joinClientTaskTx, 0);

            // Loop monitoring client connexion and byte lwip reception
            while ((E_LOG_CLIENT_CONNECTED == p->status) && (pdFAIL == xSemaphoreTake(p->quitRequestTaskMonitor, 0)))
            {
                // Raz event
                FD_ZERO(&rdfs);
                FD_SET(p->socket, &rdfs);

                // Update periodic timer
                timeout.tv_sec = 0;
                timeout.tv_usec = 1000 * ((xTimeToWait * 1000) / configTICK_RATE_HZ);

                // Monitoring socket
                if (lwip_select(p->socket + 1, &rdfs, NULL, NULL, &timeout) == -1) // Check deconnexion
                {
                    p->status = E_LOG_CLIENT_DISCONNECTED;
                }
                else
                {
                    // Check if data arrived
                    if (FD_ISSET(p->socket, &rdfs))
                    {
                        nbBytesReceived = lwip_recv(p->socket,           //
                                                    p->bufferRX,         //
                                                    sizeof(p->bufferRX), //
                                                    MSG_DONTWAIT);       //

                        // Check deconnexion
                        if (nbBytesReceived <= 0)
                        {
                            p->status = E_LOG_CLIENT_DISCONNECTED;
                        }
                        else
                        {
                            // Update rx activity
                            p->timeoutActivite = 0;

                            // Send to analyzer, flush if overflow
                            resChannelSent = E_CHANNEL_RESULT_OK;
                            for (wIterSent = 0;                                                            //
                                 (wIterSent < nbBytesReceived) && (resChannelSent == E_CHANNEL_RESULT_OK); //
                                 wIterSent += nbBytesSent)                                                 //
                            {
                                resChannelSent = P_CHANNEL_Send(&p->channelInput,                       //
                                                                &p->bufferRX[wIterSent],                //
                                                                (uint16_t) nbBytesReceived - wIterSent, //
                                                                &nbBytesSent,                           //
                                                                E_CHANNEL_WR_MODE_NORMAL);              //

                                if (resChannelSent == E_CHANNEL_RESULT_ERROR_FULL)
                                {
                                    P_CHANNEL_Flush(&p->channelInput);
                                }
                            }
                        }

                        xTaskCheckForTimeOut(&xTimeOut, &xTimeToWait); //---Period reajust
                    }
                    else
                    {
                        vTaskSetTimeOutState(&xTimeOut); //---Period restart
                        timeout.tv_sec = 0;
                        timeout.tv_usec = 1000 * P_LOG_CLT_MONITOR_PERIOD;
                        xTimeToWait = pdMS_TO_TICKS(P_LOG_CLT_MONITOR_PERIOD);

                        //-------------------------Periodic zone--------------------------------
                        p->timeoutActivite++;
                        if (p->timeoutActivite >= p->trigTimeoutActivite)
                        {
                            p->timeoutActivite = 0;
                            if (p->trigTimeoutActivite > 0)
                            {
                                p->status = E_LOG_CLIENT_DISCONNECTED;
                            }
                        }

                        xTaskCheckForTimeOut(&xTimeOut, &xTimeToWait); //---Period reajust
                    }
                }
            }

            // Flush channel, status disconnected, send signal to created task and join it
            P_CHANNEL_Flush(&p->channelOutput);
            p->status = E_LOG_CLIENT_DISCONNECTED;
            xSemaphoreGive(p->quitRequestTaskTx);
            xSemaphoreTake(p->joinClientTaskTx, portMAX_DELAY);
        }
        else
        {
            p->status = E_LOG_CLIENT_DISCONNECTED;
        }

        // Destroy socket
        if (p->socket != -1)
        {
            lwip_shutdown(p->socket, SHUT_RDWR);
            lwip_close(p->socket);
            DEBUG_decrementCpt();
            p->socket = -1;
        }

        // Send signal to server
        xSemaphoreGive(p->joinClientTaskMonitor);
    }
    DEBUG_decrementCpt();
    vTaskDelete(NULL);
}

// Client destruction. Call by server task.
static void ClientStopThenDestroy(tLogClientWks** p)
{
    if ((p != NULL) && ((*p) != NULL))
    {
        // Overwrite status
        (*p)->status = E_LOG_CLIENT_DISCONNECTED;

        // Send quit request to server task
        if (NULL != (*p)->quitRequestTaskMonitor)
        {
            xSemaphoreGive((*p)->quitRequestTaskMonitor);
        }

        // Wait for server task termination
        if (NULL != (*p)->joinClientTaskMonitor)
        {
            xSemaphoreTake((*p)->joinClientTaskMonitor, portMAX_DELAY);
        }

        // Join signals destruction
        if (NULL != (*p)->joinClientTaskMonitor)
        {
            vQueueDelete((*p)->joinClientTaskMonitor);
            (*p)->joinClientTaskMonitor = NULL;
            DEBUG_decrementCpt();
        }

        if (NULL != (*p)->joinClientTaskRx)
        {
            vQueueDelete((*p)->joinClientTaskRx);
            (*p)->joinClientTaskRx = NULL;
            DEBUG_decrementCpt();
        }

        if (NULL != (*p)->joinClientTaskTx)
        {
            vQueueDelete((*p)->joinClientTaskTx);
            (*p)->joinClientTaskTx = NULL;
            DEBUG_decrementCpt();
        }

        // Quit signals destruction
        if (NULL != (*p)->quitRequestTaskMonitor)
        {
            vQueueDelete((*p)->quitRequestTaskMonitor);
            (*p)->quitRequestTaskMonitor = NULL;
            DEBUG_decrementCpt();
        }
        if (NULL != (*p)->quitRequestTaskRx)
        {
            vQueueDelete((*p)->quitRequestTaskRx);
            (*p)->quitRequestTaskRx = NULL;
            DEBUG_decrementCpt();
        }

        if (NULL != (*p)->quitRequestTaskTx)
        {
            vQueueDelete((*p)->quitRequestTaskTx);
            (*p)->quitRequestTaskTx = NULL;
            DEBUG_decrementCpt();
        }

        // Socket destruction
        if ((-1) != (*p)->socket)
        {
            lwip_shutdown((*p)->socket, SHUT_RDWR);
            lwip_close((*p)->socket);
            (*p)->socket = -1;
            DEBUG_decrementCpt();
        }

        // Channels destruction
        P_CHANNEL_DeInit(&(*p)->channelOutput);
        P_CHANNEL_DeInit(&(*p)->channelInput);

        // Workspace destruction
        (void) memset(*p, 0, sizeof(tLogClientWks));
        vPortFree(*p);
        *p = NULL;
        DEBUG_decrementCpt();
    }
}

// Client workspace creation
static tLogClientWks* ClientCreateThenStart(int32_t socket,
                                            tLogSrvWks* pServ,
                                            uint32_t timeoutS,
                                            ptrFct_AnalyzerContextCreation cbAnalyzerContextCreationCallback,
                                            ptrFct_AnalyzerContextDestruction cbAnalyzerContextDestructionCallback,
                                            ptrFct_AnalyzerCallback cbAnalyzerCallback,
                                            ptrFct_AnalyzerPeriodic cbAnalyzerTimeOutCallback,

                                            ptrFct_EncoderContextCreation cbSenderContextCreation,
                                            ptrFct_EncoderContextDestruction cbSenderContextDestruction,
                                            ptrFct_EncoderCallback cbSenderCallback,
                                            ptrFct_EncoderPeriodicCallback cbSenderTimeoutCallback)
{
    tLogClientWks* pClt = NULL;
    eChannelResult resFifo = E_CHANNEL_RESULT_NOK;

    if (NULL == pServ)
    {
        return NULL;
    }

    // Workspace creation
    pClt = pvPortMalloc(sizeof(tLogClientWks));
    if (pClt == NULL)
    {
        return NULL;
    }
    memset(pClt, 0, sizeof(tLogClientWks));

    DEBUG_incrementCpt();

    // Backup socket value
    pClt->socket = socket;
    // Create signals
    pClt->joinClientTaskMonitor = xSemaphoreCreateBinary();
    pClt->joinClientTaskTx = xSemaphoreCreateBinary();
    pClt->joinClientTaskRx = xSemaphoreCreateBinary();
    pClt->quitRequestTaskMonitor = xSemaphoreCreateBinary();
    pClt->quitRequestTaskRx = xSemaphoreCreateBinary();
    pClt->quitRequestTaskTx = xSemaphoreCreateBinary();

    // Set callbacks value
    pClt->cbAnalyzer = cbAnalyzerCallback;
    pClt->cbAnalyzerContextCreation = cbAnalyzerContextCreationCallback;
    pClt->cbAnalyzerContextDestruction = cbAnalyzerContextDestructionCallback;
    pClt->cbAnalyzerPeriodic = cbAnalyzerTimeOutCallback;

    pClt->cbEncoder = cbSenderCallback;
    pClt->cbEncoderContextCreation = cbSenderContextCreation;
    pClt->cbEncoderContextDestruction = cbSenderContextDestruction;
    pClt->cbEncoderPeriodic = cbSenderTimeoutCallback;

    // Contexts raz.
    pClt->ptrAnalyzerContext = NULL;
    pClt->ptrEncoderContext = NULL;

    // Raz timeout value
    pClt->trigTimeoutActivite = (1000 * timeoutS) / P_LOG_CLT_MONITOR_PERIOD;
    pClt->timeoutActivite = 0;
    pClt->bActiviteRx = 0;
    pClt->bActiviteTx = 0;

    // Save server handle
    pClt->pServer = pServ;

    // Set client status
    pClt->status = E_LOG_CLIENT_CONNECTED;

    // Initialize channels input / output
    resFifo = P_CHANNEL_Init(&pClt->channelInput,     //
                             P_LOG_FIFO_DATA_SIZE,    //
                             P_LOG_FIFO_ELT_MAX_SIZE, //
                             P_LOG_FIFO_MAX_NB_ELT);  //

    if (E_CHANNEL_RESULT_OK == resFifo)
    {
        resFifo = P_CHANNEL_Init(&pClt->channelOutput,    //
                                 P_LOG_FIFO_DATA_SIZE,    //
                                 P_LOG_FIFO_ELT_MAX_SIZE, //
                                 P_LOG_FIFO_MAX_NB_ELT);  //
    }

    // Check signals creation
    if ((NULL == pClt->joinClientTaskMonitor) || (NULL == pClt->joinClientTaskTx) || (NULL == pClt->joinClientTaskRx) ||
        (NULL == pClt->quitRequestTaskMonitor) || (NULL == pClt->quitRequestTaskRx) ||
        (NULL == pClt->quitRequestTaskTx) || (E_CHANNEL_RESULT_OK != resFifo))
    {
        ClientStopThenDestroy(&pClt);
        return NULL;
    }

    DEBUG_incrementCpt();
    DEBUG_incrementCpt();
    DEBUG_incrementCpt();
    DEBUG_incrementCpt();
    DEBUG_incrementCpt();
    DEBUG_incrementCpt();

    // Raz signals
    xSemaphoreTake(pClt->joinClientTaskMonitor, 0);
    xSemaphoreTake(pClt->joinClientTaskTx, 0);
    xSemaphoreTake(pClt->joinClientTaskRx, 0);
    xSemaphoreTake(pClt->quitRequestTaskMonitor, 0);
    xSemaphoreTake(pClt->quitRequestTaskRx, 0);
    xSemaphoreTake(pClt->quitRequestTaskTx, 0);

    // Give join signal in case of creation of task failure
    xSemaphoreGive(pClt->joinClientTaskMonitor);
    if (xTaskCreate(cbTaskSocketClientRxAndMon,          //
                    "logClt",                            //
                    P_LOG_CLT_MON_CALLBACK_STACK,        //
                    pClt,                                //
                    configMAX_PRIORITIES - 1,            //
                    &pClt->handleTaskMonitor) != pdPASS) //
    {
        ClientStopThenDestroy(&pClt);
        return NULL;
    }
    else
    {
        // Task well launched, raz join signal
        DEBUG_incrementCpt();
        xSemaphoreTake(pClt->joinClientTaskMonitor, 0);
    }

    return pClt;
}

static void cbTaskSocketServerMonAndLog(void* pParameters)
{
    tLogSrvWks* p = (tLogSrvWks*) pParameters; // Server workspace
    tLogClientWks* pClt = NULL;                // Temp client workspace

    SOPC_ReturnStatus resList = SOPC_STATUS_OK;
    eChannelResult resChannel = E_CHANNEL_RESULT_OK;
    eChannelResult resChannelSent = E_CHANNEL_RESULT_OK;

    TimeOut_t xTimeOut = {0, 0}; // Timeout use for periodic call of task
    TickType_t xTimeToWait = 0;  // Timeout use for lwip select timeout adjust for periodic call of task
    uint16_t nbBytesToSend = 0;  // Nb Bytes to send
    uint16_t nbBytesSent = 0;
    int16_t byteSent = 0; // Nb byte sent by lwip api
    uint16_t wIter = 0;   // Mute iterator
    uint16_t wIterSent = 0;

    int32_t csock = -1;  // Temp new client socket
    int32_t opt = 1;     // set opt
    int32_t resLwip = 0; // lwip api returns

    struct sockaddr_in sin = {0};
    struct timeval lwipTimeOut = {0, 0};
    socklen_t sinsize = sizeof(sin);
    struct fd_set rdfs;
    ip_addr_t localeAddress;

    memset(&localeAddress, 0, sizeof(ip_addr_t));
    FD_ZERO(&rdfs);

    vTaskSetTimeOutState(&xTimeOut);
    xTimeToWait = pdMS_TO_TICKS(P_LOG_SRV_ONLINE_PERIOD); // Initialize period

    if (NULL != p)
    {
        // Server loop, quit if request or CLOSING status
        while ((E_LOG_SERVER_CLOSING != p->status) && (pdFALSE == xSemaphoreTake(p->quitRequest, 0)))
        {
            switch (p->status)
            {
            case E_LOG_SERVER_BINDING:
            {
                resLwip = -1;

                // Check if ethernet is ready
                if (ETHERNET_IF_RESULT_OK == P_ETHERNET_IF_IsReady(0))
                {
                    // Create tcp socket then bind
                    p->socketTCP = lwip_socket(AF_INET, SOCK_STREAM, 0);
                    if (p->socketTCP >= 0)
                    {
                        DEBUG_incrementCpt();
                        resLwip = lwip_setsockopt(p->socketTCP, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
                        if (resLwip == 0)
                        {
                            (void) memset(&sin, 0, sizeof(struct sockaddr_in));
                            sin.sin_addr.s_addr = htonl(INADDR_ANY);
                            sin.sin_family = AF_INET;
                            sin.sin_port = htons(p->port);

                            lwip_bind(p->socketTCP, (struct sockaddr*) &sin, sizeof(struct sockaddr_in));
                            if (resLwip == 0)
                            {
                                resLwip = lwip_listen(p->socketTCP, p->maxClient);
                            }
                        }
                    }
                }

                // If binding ok , go to online status, raz select period
                if (0 == resLwip)
                {
                    p->status = E_LOG_SERVER_ONLINE;
                    // Set timeout select
                    vTaskSetTimeOutState(&xTimeOut);
                    lwipTimeOut.tv_sec = 0;
                    lwipTimeOut.tv_usec = 1000 * P_LOG_SRV_ONLINE_PERIOD;
                    xTimeToWait = pdMS_TO_TICKS(P_LOG_SRV_ONLINE_PERIOD);
                }
                else
                {
                    // Destroy socket in case of error
                    if (p->socketTCP >= 0)
                    {
                        lwip_shutdown(p->socketTCP, SHUT_RDWR);
                        lwip_close(p->socketTCP);
                        DEBUG_decrementCpt();
                        p->socketTCP = -1;
                    }
                    // Wait for 100 ms before retry
                    p->status = E_LOG_SERVER_BINDING;
                    vTaskDelay(pdMS_TO_TICKS(P_LOG_SRV_BINDING_WAIT));
                }
            }
            break;
            case E_LOG_SERVER_ONLINE:
            {
                // Reset fd server
                FD_ZERO(&rdfs);
                // Add server to fd
                FD_SET(p->socketTCP, &rdfs);
                // Timeout
                lwipTimeOut.tv_sec = 0;
                lwipTimeOut.tv_usec = 1000 * ((xTimeToWait * 1000) / configTICK_RATE_HZ);
                // New connection monitoring
                resLwip = lwip_select(p->socketTCP + 1, //
                                      &rdfs,            //
                                      NULL,             //
                                      NULL,             //
                                      &lwipTimeOut);    //
                if (resLwip < 0)
                {
                    FD_ZERO(&rdfs);
                    FD_SET(p->socketTCP, &rdfs);
                }

                //----------------------------------------------Event part
                if (FD_ISSET(p->socketTCP, &rdfs))
                {
                    // Accept connexion
                    pClt = NULL;
                    csock = -1;
                    memset(&sin, 0, sinsize);

                    csock = lwip_accept(p->socketTCP, (struct sockaddr*) &sin, &sinsize);
                    if (csock != -1)
                    {
                        // Disable naggle algorithm
                        configASSERT(lwip_setsockopt(csock,              //
                                                     IPPROTO_TCP,        //
                                                     TCP_NODELAY,        //
                                                     (const void*) &opt, //
                                                     sizeof(opt)) == 0); //

                        DEBUG_incrementCpt();

                        // Check if free slot exist
                        if (P_UTILS_LIST_GetNbEltMT(&p->clientList) < p->maxClient)
                        {
                            // Create client workspace + thread...
                            pClt = ClientCreateThenStart(csock,                                 //
                                                         p,                                     //
                                                         p->timeoutClientS,                     //
                                                         p->cbClientAnalyzerContextCreation,    //
                                                         p->cbClientAnalyzerContextDestruction, //
                                                         p->cbClientAnalyzer,                   //
                                                         p->cbClientAnalyzerPeriodic,           //
                                                         p->cbClientEncoderContextCreation,     //
                                                         p->cbClientEncoderContextDestruction,  //
                                                         p->cbClientEncoder,                    //
                                                         p->cbClientEncoderPeriodic);           //
                            if (pClt != NULL)
                            {
                                resList = P_UTILS_LIST_AddEltMT(&p->clientList, pClt, NULL, 0, 0);
                                if (resList != SOPC_STATUS_OK)
                                {
                                    ClientStopThenDestroy(&pClt);
                                }
                            }
                        }
                        else
                        {
                            lwip_shutdown(csock, SHUT_RDWR);
                            lwip_close(csock);
                            DEBUG_decrementCpt();
                        }

                        pClt = NULL;
                        csock = -1;
                        memset(&sin, 0, sinsize);
                    }
                    // Reajust timeout for periodic treatment
                    xTaskCheckForTimeOut(&xTimeOut, &xTimeToWait); //---Period reajust
                }
                else
                {
                    // Periodic treatment or timeout
                    vTaskSetTimeOutState(&xTimeOut);
                    lwipTimeOut.tv_sec = 0;
                    lwipTimeOut.tv_usec = 1000 * P_LOG_SRV_ONLINE_PERIOD;
                    xTimeToWait = pdMS_TO_TICKS(P_LOG_SRV_ONLINE_PERIOD);

                    //----------------------------------------------Periodic part

                    // Check if clients are disconnected then destroy it if necessary
                    wIter = USHRT_MAX;
                    do
                    {
                        pClt = P_UTILS_LIST_ParseValueEltMT(&p->clientList, NULL, NULL, NULL, &wIter);
                        if (pClt != NULL)
                        {
                            if (pClt->status != E_LOG_CLIENT_CONNECTED)
                            {
                                P_UTILS_LIST_RemoveEltMT(&p->clientList, pClt, 0, 0, &wIter);
                                ClientStopThenDestroy(&pClt);
                            }
                        }
                    } while (wIter != USHRT_MAX);

                    // Check if log message arrived
                    memset(p->bufferSRV_TX, 0, sizeof(p->bufferSRV_TX));

                    nbBytesToSend = 0;

                    resChannel = P_CHANNEL_Receive(&p->broadCastChannel,      //
                                                   NULL,                      //
                                                   &p->bufferSRV_TX[0],       //
                                                   &nbBytesToSend,            //
                                                   sizeof(p->bufferSRV_TX),   //
                                                   0,                         //
                                                   E_CHANNEL_RD_MODE_NORMAL); //

                    // Send message to all connected client. Quit loop if error.
                    while ((E_CHANNEL_RESULT_OK == resChannel) || (E_CHANNEL_RESULT_MORE_DATA == resChannel))
                    {
                        wIter = UINT16_MAX;
                        do
                        {
                            pClt = P_UTILS_LIST_ParseValueEltMT(&p->clientList, NULL, NULL, NULL, &wIter);
                            if (pClt != NULL)
                            {
                                if (pClt->status == E_LOG_CLIENT_CONNECTED)
                                {
                                    resChannelSent = E_CHANNEL_RESULT_OK;
                                    for (wIterSent = 0;                                                          //
                                         (wIterSent < nbBytesToSend) && (resChannelSent == E_CHANNEL_RESULT_OK); //
                                         wIterSent += nbBytesToSend)                                             //
                                    {
                                        resChannelSent = P_CHANNEL_Send(&pClt->channelOutput,        //
                                                                        &p->bufferSRV_TX[wIterSent], //
                                                                        nbBytesToSend - wIterSent,   //
                                                                        &nbBytesSent,                //
                                                                        E_CHANNEL_WR_MODE_NORMAL);   //
                                    }

                                    if (resChannelSent == E_CHANNEL_RESULT_ERROR_FULL)
                                    {
                                        P_CHANNEL_Flush(&pClt->channelOutput);
                                    }
                                }
                            }
                        } while (wIter != UINT16_MAX);

                        // Receive next message
                        memset(p->bufferSRV_TX, 0, sizeof(p->bufferSRV_TX));

                        resChannel = P_CHANNEL_Receive(&p->broadCastChannel,      //
                                                       NULL,                      //
                                                       &p->bufferSRV_TX[0],       //
                                                       &nbBytesToSend,            //
                                                       sizeof(p->bufferSRV_TX),   //
                                                       0,                         //
                                                       E_CHANNEL_RD_MODE_NORMAL); //
                    }

                    // Check timeeout for announce ip and port of server to all client listing UDP port 4023
                    p->timerHello++;
                    if (p->timerHello >= p->periodeHello)
                    {
                        p->timerHello = 0;
                        if (p->periodeHello > 0)
                        {
                            if (P_ETHERNET_IF_GetIp(&localeAddress) ==
                                ETHERNET_IF_RESULT_OK) // Only if ethernet initialized
                            {
                                // Create socket
                                p->socketUDP = lwip_socket(AF_INET, SOCK_DGRAM, 0);
                                if (p->socketUDP >= 0)
                                {
                                    DEBUG_incrementCpt();
                                    if (localeAddress.type == 0)
                                    {
                                        memset(&sin, 0, sizeof(struct sockaddr_in));
                                        memset(p->bufferSRV_TX, 0, sizeof(p->bufferSRV_TX));
                                        sin.sin_addr.s_addr = htonl(INADDR_BROADCAST);
                                        sin.sin_family = AF_INET;
                                        sin.sin_port = htons(p->portHello);
                                        ipaddr_ntoa_r(&localeAddress,
                                                      (void*) p->bufferSRV_TX + sizeof(p->bufferSRV_TX) / 2,
                                                      sizeof(p->bufferSRV_TX) / 2);

                                        sprintf((void*) p->bufferSRV_TX, "%s:%d\r\n",
                                                p->bufferSRV_TX + sizeof(p->bufferSRV_TX) / 2, p->port);

                                        if (p->cbEncoderTransmitHello != NULL)
                                        {
                                            nbBytesToSend = p->cbEncoderTransmitHello(p->bufferSRV_TX,
                                                                                      strlen((void*) p->bufferSRV_TX),
                                                                                      sizeof(p->bufferSRV_TX));
                                        }
                                        else
                                        {
                                            nbBytesToSend = strlen((void*) p->bufferSRV_TX);
                                        }

                                        if (nbBytesToSend <= sizeof(p->bufferSRV_TX))
                                        {
                                            byteSent = 0;
                                            for (wIter = 0; (wIter < nbBytesToSend) && (byteSent >= 0);
                                                 wIter += (uint16_t) byteSent)
                                            {
                                                byteSent = lwip_sendto(p->socketUDP,                //
                                                                       p->bufferSRV_TX + wIter,     //
                                                                       nbBytesToSend - wIter,       //
                                                                       0,                           //
                                                                       (struct sockaddr*) &sin,     //
                                                                       sizeof(struct sockaddr_in)); //
                                            }
                                        }
                                    }

                                    // Destroy socket
                                    lwip_close(p->socketUDP);
                                    DEBUG_decrementCpt();
                                    p->socketUDP = -1;
                                }
                            }
                        }
                    }

                    xTaskCheckForTimeOut(&xTimeOut, &xTimeToWait); //---Reajust timeout for periodic treatment
                }
            }
            break;
            default:
            {
                // Nothing
            }
            break;
            }
        }

        p->status = E_LOG_SERVER_CLOSING;

        // Status closing or quit request, quit all client then shutdown srv sockets.

        wIter = UINT16_MAX;

        do
        {
            pClt = P_UTILS_LIST_ParseValueEltMT(&p->clientList, //
                                                NULL,           //
                                                NULL,           //
                                                NULL,           //
                                                &wIter);        //
            if (pClt != NULL)
            {
                P_UTILS_LIST_RemoveEltMT(&p->clientList, pClt, 0, 0, &wIter);
                ClientStopThenDestroy(&pClt);
            }
        } while (wIter != UINT16_MAX);

        // Destroy sockets

        if (p->socketTCP >= 0)
        {
            lwip_shutdown(p->socketTCP, SHUT_RDWR);
            lwip_close(p->socketTCP);
            DEBUG_decrementCpt();
            p->socketTCP = -1;
        }

        if (p->socketUDP >= 0)
        {
            lwip_close(p->socketUDP);
            DEBUG_decrementCpt();
            p->socketUDP = -1;
        }

        // Signal server is terminated
        xSemaphoreGive(p->joinServerTask);
    }

    DEBUG_decrementCpt();
    vTaskDelete(NULL);
}

// Log function
eLogSrvResult P_LOG_SRV_SendToAllClient(tLogSrvWks* p, const uint8_t* pBuffer, uint16_t length, uint16_t* sentLength)
{
    eLogSrvResult result = E_LOG_SRV_RESULT_NOK;
    eChannelResult resChannelSent = E_CHANNEL_RESULT_OK;
    uint16_t wIterSent = 0;
    uint16_t nbBytesSent = 0;
    uint16_t totalBytesSent = 0;

    if ((NULL != p) && (E_LOG_SERVER_ONLINE == p->status))
    {
        resChannelSent = E_CHANNEL_RESULT_OK;
        for (wIterSent = 0; (wIterSent < length) && (E_CHANNEL_RESULT_OK == resChannelSent); wIterSent += nbBytesSent)
        {
            resChannelSent = P_CHANNEL_Send(&p->broadCastChannel,      //
                                            pBuffer + wIterSent,       //
                                            length - wIterSent,        //
                                            &nbBytesSent,              //
                                            E_CHANNEL_WR_MODE_NORMAL); //

            if (E_CHANNEL_RESULT_ERROR_FULL == resChannelSent)
            {
                P_CHANNEL_Flush(&p->broadCastChannel);
            }
            else
            {
                totalBytesSent += nbBytesSent;
            }
        }
        if (E_CHANNEL_RESULT_OK == resChannelSent)
        {
            result = E_LOG_SRV_RESULT_OK;
        }
    }
    if (NULL != sentLength)
    {
        *sentLength = totalBytesSent;
    }

    return result;
}

// Server destruction
void P_LOG_SRV_StopAndDestroy(tLogSrvWks** p)
{
    if ((NULL != p) && (NULL != (*p)))
    {
        P_CHANNEL_Flush(&(*p)->broadCastChannel);

        (*p)->status = E_LOG_SERVER_CLOSING;

        if (NULL != (*p)->quitRequest)
        {
            xSemaphoreGive((*p)->quitRequest);
        }

        if (NULL != (*p)->joinServerTask)
        {
            xSemaphoreTake((*p)->joinServerTask, portMAX_DELAY);
        }

        P_CHANNEL_DeInit(&(*p)->broadCastChannel);

        if (NULL != (*p)->quitRequest)
        {
            vQueueDelete((*p)->quitRequest);
            (*p)->quitRequest = NULL;
            DEBUG_decrementCpt();
        }

        if (NULL != (*p)->joinServerTask)
        {
            vQueueDelete((*p)->joinServerTask);
            (*p)->joinServerTask = NULL;
            DEBUG_decrementCpt();
        }

        P_UTILS_LIST_DeInitMT(&(*p)->clientList);
        (void) memset(*p, 0, sizeof(tLogSrvWks));
        vPortFree(*p);
        *p = NULL;
        DEBUG_decrementCpt();
    }
}

// Server creation
tLogSrvWks* P_LOG_SRV_CreateAndStart(uint16_t port,
                                     uint16_t portHello,
                                     int16_t maxClient,
                                     uint32_t timeoutS,
                                     uint32_t periodeHelloS,

                                     ptrFct_AnalyzerContextCreation cbAnalyzerContextCreationCallback,
                                     ptrFct_AnalyzerContextDestruction cbAnalyzerContextDestructionCallback,
                                     ptrFct_AnalyzerCallback cbAnalyzerCallback,
                                     ptrFct_AnalyzerPeriodic cbAnalyzerTimeOutCallback,

                                     ptrFct_EncoderContextCreation cbSenderContextCreation,
                                     ptrFct_EncoderContextDestruction cbSenderContextDestruction,
                                     ptrFct_EncoderCallback cbSenderCallback,
                                     ptrFct_EncoderPeriodicCallback cbSenderTimeoutCallback,

                                     ptrFct_EncoderTransmitHelloCallback cbSenderHelloCallback)
{
    tLogSrvWks* p = (tLogSrvWks*) pvPortMalloc(sizeof(tLogSrvWks));
    eChannelResult resFifo = E_CHANNEL_RESULT_NOK;

    if (NULL == p)
    {
        return NULL;
    }

    DEBUG_incrementCpt();

    memset(p, 0, sizeof(tLogSrvWks));
    p->socketTCP = -1;
    p->socketUDP = -1;
    p->port = port;
    p->portHello = portHello;
    p->maxClient = maxClient;
    p->periodeHello = (periodeHelloS * 1000) / P_LOG_SRV_ONLINE_PERIOD;
    p->timerHello = 0;
    p->timeoutClientS = timeoutS;

    p->cbClientAnalyzer = cbAnalyzerCallback;
    p->cbClientAnalyzerContextCreation = cbAnalyzerContextCreationCallback;
    p->cbClientAnalyzerContextDestruction = cbAnalyzerContextDestructionCallback;
    p->cbClientAnalyzerPeriodic = cbAnalyzerTimeOutCallback;

    p->cbClientEncoder = cbSenderCallback;
    p->cbClientEncoderContextCreation = cbSenderContextCreation;
    p->cbClientEncoderContextDestruction = cbSenderContextDestruction;
    p->cbClientEncoderPeriodic = cbSenderTimeoutCallback;

    p->cbEncoderTransmitHello = cbSenderHelloCallback;

    p->status = E_LOG_SERVER_BINDING;

    resFifo = P_CHANNEL_Init(&p->broadCastChannel,    //
                             P_LOG_FIFO_DATA_SIZE,    //
                             P_LOG_FIFO_ELT_MAX_SIZE, //
                             P_LOG_FIFO_MAX_NB_ELT);  //

    if (E_CHANNEL_RESULT_OK != resFifo)
    {
        P_LOG_SRV_StopAndDestroy(&p);
        return p;
    }

    p->joinServerTask = xSemaphoreCreateBinary();
    if (p->joinServerTask == NULL)
    {
        P_LOG_SRV_StopAndDestroy(&p);
        return p;
    }
    DEBUG_incrementCpt();

    p->quitRequest = xSemaphoreCreateBinary();
    if (p->quitRequest == NULL)
    {
        P_LOG_SRV_StopAndDestroy(&p);
        return p;
    }
    DEBUG_incrementCpt();

    // Raz quit signal
    xSemaphoreTake(p->quitRequest, 0);

    if (P_UTILS_LIST_InitMT(&p->clientList, maxClient) != 0)
    {
        P_LOG_SRV_StopAndDestroy(&p);
        return p;
    }

    // Give join for delete
    xSemaphoreGive(p->joinServerTask);
    if (xTaskCreate(cbTaskSocketServerMonAndLog, //
                    "logSrv",                    //
                    P_LOG_SRV_CALLBACK_STACK,    //
                    p,                           //
                    configMAX_PRIORITIES - 1,    //
                    &p->handleTask) != pdPASS)   //
    {
        P_LOG_SRV_StopAndDestroy(&p);
        return p;
    }
    else
    {
        DEBUG_incrementCpt();
        // Raz join signal
        xSemaphoreTake(p->joinServerTask, 0);
    }

    return p;
}

// Send response to a client
eLogSrvResult P_LOG_CLIENT_SendResponse(tLogClientWks* pClt,
                                        const uint8_t* pBuffer,
                                        uint16_t length,
                                        uint16_t* pNbBytesSent)
{
    eLogSrvResult result = E_LOG_SRV_RESULT_NOK;
    uint16_t nbBytesSent = 0;

    if (pClt == NULL)
    {
        return result;
    }

    if (P_CHANNEL_Send(&pClt->channelOutput, pBuffer, length, &nbBytesSent, E_CHANNEL_WR_MODE_NORMAL) ==
        E_CHANNEL_RESULT_OK)
    {
        result = E_LOG_SRV_RESULT_OK;
    }

    if (pNbBytesSent != NULL)
    {
        *pNbBytesSent = nbBytesSent;
    }

    return result;
}

//***********S2OPC api wrapper*************

static tLogSrvWks* gLogServer = NULL;
static Mutex gLockLogServer = NULL;
static Condition gSignalOneConnexion;

// Callback used by logserv to customize hello message
static uint16_t cbHelloCallback(uint8_t* pBufferInOut, uint16_t nbBytesToEncode, uint16_t maxSizeBufferOut)
{
    uint16_t size;

    snprintf((void*) pBufferInOut + nbBytesToEncode, maxSizeBufferOut - (2 * nbBytesToEncode + 1), "%s",
             "Hello, S2OPC log server is listening on ");
    size = strlen((void*) pBufferInOut + nbBytesToEncode);
    memmove((void*) pBufferInOut + nbBytesToEncode + size, (void*) pBufferInOut, nbBytesToEncode);
    memmove((void*) pBufferInOut, (void*) pBufferInOut + nbBytesToEncode, nbBytesToEncode + size);
    return nbBytesToEncode + size;
}

// Callback used to unlock SOPC_LogSrv_WaitClient function
static void cbOneConnexion(void** pAnalyzerContext, tLogClientWks* pClt)
{
    Condition_SignalAll(&gSignalOneConnexion);
}

// Callback used by analyzer, so *dataSize not changed, buffer in copy to buffer out to client
static eResultDecoder cbEchoCallback(void* pAnalyzerContext,
                                     tLogClientWks* pClt,
                                     uint8_t* pBufferInOut,
                                     uint16_t* dataSize,
                                     uint16_t maxSizeBufferOut)
{
    // Don't modify dataSize output, echo simulation
    return 0;
}

// Wait a client connexion.
SOPC_ReturnStatus SOPC_LogSrv_WaitClient(uint32_t timeoutMs)
{
    SOPC_ReturnStatus status = SOPC_STATUS_OK;
    if (NULL == gLockLogServer)
    {
        return SOPC_STATUS_NOK;
    }

    Mutex_Lock(&gLockLogServer);

    if (gLogServer == NULL)
    {
        Mutex_Unlock(&gLockLogServer);
        return SOPC_STATUS_NOK;
    }

    status = Mutex_UnlockAndTimedWaitCond(&gSignalOneConnexion, &gLockLogServer, timeoutMs);

    Mutex_Unlock(&gLockLogServer);

    return status;
}

// Stop log server
SOPC_ReturnStatus SOPC_LogSrv_Stop(void)
{
    SOPC_ReturnStatus status = SOPC_STATUS_OK;
    if (NULL == gLockLogServer)
    {
        return SOPC_STATUS_NOK;
    }

    Mutex_Lock(&gLockLogServer);

    if (NULL == gLogServer)
    {
        Mutex_Unlock(&gLockLogServer);
        return SOPC_STATUS_NOK;
    }

    Condition_Clear(&gSignalOneConnexion);

    P_LOG_SRV_StopAndDestroy(&gLogServer);

    Mutex_Unlock(&gLockLogServer);

    return status;
}

// Start log server
SOPC_ReturnStatus SOPC_LogSrv_Start(
    uint16_t portSrvTCP, // Server listen port
    uint16_t portCltUDP) // Destination UDP port where server announce its @IP and listen port
{
    SOPC_ReturnStatus status = SOPC_STATUS_OK;

    if (gLockLogServer == NULL)
    {
        status = Mutex_Initialization(&gLockLogServer);
    }

    if (SOPC_STATUS_OK != status)
    {
        return SOPC_STATUS_NOK;
    }

    Mutex_Lock(&gLockLogServer);

    if (SOPC_STATUS_OK != status)
    {
        Mutex_Unlock(&gLockLogServer);
        return status;
    }

    if (gLogServer == NULL)
    {
        status = Condition_Init(&gSignalOneConnexion);

        gLogServer = P_LOG_SRV_CreateAndStart(portSrvTCP,       //
                                              portCltUDP,       //
                                              2,                // Max log client
                                              0,                // Disconnect log client after 0s
                                              5,                // Hello message each 5seconds
                                              cbOneConnexion,   //
                                              NULL,             //
                                              cbEchoCallback,   // Test echo to verify lwip
                                              NULL,             //
                                              NULL,             //
                                              NULL,             //
                                              NULL,             //
                                              NULL,             //
                                              cbHelloCallback); // Customize message hello

        if (gLogServer == NULL)
        {
            status = SOPC_STATUS_NOK;
        }
    }

    Mutex_Unlock(&gLockLogServer);

    return status;
}

//*********Wrappers for newlib**************

int __attribute__((weak)) _open(const char* Path, int flags, int mode)
{
    return (int) stdout->_file;
}

int __attribute__((weak)) _open_r(struct _reent* reent, const char* Path, int flags, int mode)
{
    return _open(Path, flags, mode);
}

int __attribute__((weak)) _close(int fd)
{
    return 0;
}

int __attribute__((weak)) _close_r(struct _reent* reent, int fd)
{
    return _close(fd);
}

FILE* __attribute__((weak)) fopen(const char* file, const char* mode)
{
    return (FILE*) stdout;
}

FILE* __attribute__((weak)) _fopen_r(struct _reent* reent, const char* file, const char* mode)
{
    return fopen(file, mode);
}

int __attribute__((weak)) fclose(FILE* ptrFile)
{
    return 0;
}

int __attribute__((weak)) _fclose_r(struct _reent* reent, FILE* ptrFile)
{
    return 0;
}

int __attribute__((weak)) _write(int handle, const char* buffer, size_t size)
{
    uint16_t length;

    // buffer exist
    if (buffer == 0)
    {
        return -1;
    }

    // Stdout or stdin only are redirected
    if ((handle != 1) && (handle != 2))
    {
        return -1;
    }
    // Log server exist
    if (NULL == gLogServer || E_LOG_SERVER_ONLINE != gLogServer->status)
    {
        length = PRINTF(buffer, size);
    }
    else
    {
        /* Send data. */
        P_LOG_SRV_SendToAllClient(gLogServer, (uint8_t*) buffer, size, &length);
    }

    return length;
}

int __attribute__((weak)) _write_r(struct _reent* reent, int handle, const void* buffer, size_t size)
{
    return _write(handle, buffer, size);
}

// Read is not implemented.
int __attribute__((weak)) _read(int handle, char* buffer, int size)
{
    return -1;
}

int __attribute__((weak)) _read_r(struct _reent* reent, int handle, void* buffer, size_t size)
{
    return _read(handle, buffer, size);
}