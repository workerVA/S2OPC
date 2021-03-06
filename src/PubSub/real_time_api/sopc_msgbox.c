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

/// @file sopc_msgbox.c

#include "sopc_msgbox.h"

// Private types definitions

/// @brief Message box sync status, used to protect API concurrent accesses (SOPC_MsgBox_DataHandle API)
typedef enum E_MSG_BOX_INFO_SYNC
{
    E_MSG_BOX_INFO_SYNC_NOT_USED,      ///< Message box data handle is created and not initialized
    E_MSG_BOX_INFO_SYNC_USED,          ///< Message box data handle is in used
    E_MSG_BOX_INFO_SYNC_RESERVING,     ///< Message box data handle is initializing
    E_MSG_BOX_INFO_SYNC_RESERVED,      ///< Status after SOPC_MsgBox_DataHandle_Initialize
    E_MSG_BOX_INFO_SYNC_RESERVED_USED, ///< Status after SOPC_MsgBox_DataHandle_Get and Update function calling
    E_MSG_BOX_INFO_SYNC_RELEASING,     ///< Status after SOPC_MsgBox_DataHandle_Finalize
    E_MSG_BOX_INFO_SYNC_SIZE = INT32_MAX
} eMsgBoxInfoSync;

/// @brief This structure contains inUse flag used by mutual exclusion of API usage for same client id.
typedef struct T_MSG_BOX_INFO_SYNC
{
    eMsgBoxInfoSync eIsInUse; ///< Workspace using status for SOPC_MsgBox_DataHandle_XXX functions (writer side)
    bool bIsInUse; ///< Workspace using status for SOPC_MsgBox_Push and SOPC_MsgBox_GetEvtPtr API. (writer and reader
                   ///< sides)
} tMsgBoxInfoSync;

/// @brief Message box FIFO events, which contains size and offset in the buffer of data
typedef struct T_MSG_BOX_FIFO_EVENTS
{
    uint32_t size;   ///< Size of an event
    uint32_t offset; ///< Offset of the data
} __attribute__((packed)) tMsgBoxFifoEvents;

/// @brief Message box FIFO header, which contains indexes of next write of event and linked data, free space, space
/// bounds
typedef struct T_MSG_BOX_FIFO_HEADER
{
    uint32_t nbEvts;    ///< Current total events
    uint32_t nbData;    ///< Current total of data in bytes
    uint32_t idxWrEvt;  ///< Index of next event write
    uint32_t idxWrData; ///< Index of next data write
    uint32_t maxEvts;   ///< Maximum of events
    uint32_t maxData;   ///< Maximum of cumulative data
} __attribute__((packed)) tMsgBoxFifoHeader;

/// @brief Message box handle
struct SOPC_MsgBox
{
    /* Internal structure contained by an SOPC_DoubleBuffer
    tMsgBoxFifoHeader fifoHeader; // FIFO header
    tMsgBoxFifoEvents* pEvents;   // FIFO events buffer
    uint8_t* pData;               // FIFO data buffer
     */

    uint32_t doubleBufferFieldSize; ///< Double buffer size

    uint32_t nbMaxClts;           ///< Maximum of concurrent clients of message box API (Get read pointer)
    uint32_t* idxEvtReader;       ///< Table of index used by concurrent clients to identify if new event is arrived.
    tMsgBoxInfoSync* pLockReader; ///< Table of inUse flags used by concurrent clients

    tMsgBoxInfoSync lockWriter; ///< In use flag used by writer.

    SOPC_DoubleBuffer* pFifoPublisher; ///< Double buffer used to publish coherent FIFO image : tMsgBoxFifoHeader +
                                       ///< tMsgBoxFifoEvents[] + uint8_t[]
};

// Private functions declaration

/// @brief Message box reset
/// @param [in] pMsgBox Message box handle
static void SOPC_MsgBox_DeInitialize(SOPC_MsgBox* pMsgBox);

/// @brief Message box initialization
/// @param [in] pMsgBox Message box handle
/// @param [in] max_clients Max message box concurrent client. Client identifier between 0 -> max-1
/// @param [in] max_evts Max events to manage writer burst.
/// @param [in] max_data_evt Max cumulative data in bytes.
static SOPC_ReturnStatus SOPC_MsgBox_Initialize(
    SOPC_MsgBox* pMsgBox,   // Message box object
    uint32_t max_clients,   // Max message box concurrent client. Client identifier between 0 -> max-1
    uint32_t max_evts,      // Max events to manage writer burst.
    uint32_t max_data_evt); // Max cumulative data in bytes.

/// @brief Message box FIFO header update function
/// @param [inout] pFifoHeader Header structure
/// @param [inout] pFifoEvts Buffer of events
/// @param [inout] pFifoData Buffer of data
/// @param [in] pData Data to push
/// @param [in] size Size of data to push
static SOPC_ReturnStatus SOPC_MsgBox_UpdateFifoHeader(tMsgBoxFifoHeader* pFifoHeader, // Header structure
                                                      tMsgBoxFifoEvents* pFifoEvts,   // Buffer of events
                                                      uint8_t* pFifoData,             // Buffer of data
                                                      uint8_t* pData,                 // Data to push
                                                      uint32_t size);                 // Size of data to push

/// @brief Message box FIFO header reset function
/// @param [in] pFifoHeader Header structure
/// @param [in] pFifoEvts Buffer of events
/// @param [in] pFifoData Buffer of data
/// @return SOPC_STATUS_OK
static SOPC_ReturnStatus SOPC_MsgBox_ResetFifoHeader(tMsgBoxFifoHeader* pFifoHeader, // Header structure
                                                     tMsgBoxFifoEvents* pFifoEvts,   // Buffer of events
                                                     uint8_t* pFifoData);            // Buffer of data

static SOPC_ReturnStatus SOPC_MsgBox_UpdateFifoHeader(tMsgBoxFifoHeader* pFifoHeader, //
                                                      tMsgBoxFifoEvents* pFifoEvts,   //
                                                      uint8_t* pFifoData,             //
                                                      uint8_t* pData,                 //
                                                      uint32_t size)                  //
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    // Check invalid parameters
    if (pFifoHeader == NULL ||         //
        size > pFifoHeader->maxData || //
        size < 1 ||                    //
        pFifoEvts == NULL ||           //
        pFifoData == NULL ||           //
        pData == NULL)                 //
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    // Overwrite treatment. Get current write index.
    uint32_t nextSize = 0;
    uint32_t idxWr = pFifoHeader->idxWrEvt;

    // While not enough space to handle new event, get current event pointed size and all beyond this,
    // verify if size > 0. In that case, event has been previously added, decrement total of events and total data size
    // of this event size, and reset this event to 0.
    while (((pFifoHeader->nbEvts + 1) > pFifoHeader->maxEvts) || ((pFifoHeader->nbData + size) > pFifoHeader->maxData))
    {
        nextSize = pFifoEvts[idxWr].size;
        if (pFifoEvts[idxWr].size > 0)
        {
            pFifoEvts[idxWr].size = 0;
            pFifoEvts[idxWr].offset = 0;
            pFifoHeader->nbEvts = pFifoHeader->nbEvts - 1;
            pFifoHeader->nbData = pFifoHeader->nbData - nextSize;
        }

        idxWr = (idxWr + 1) % pFifoHeader->maxEvts;
    }

    // Backup current write index as new event offset field value.
    uint32_t offset = pFifoHeader->idxWrData;

    // Copy input data to data buffer and increment data write index.
    uint8_t* iterData = pData;
    while (iterData != (pData + size))
    {
        // Modulo not used, data buffer size is multiplied by 2 at initialization (max data stay set to init value).
        // At the data get pointer returned by MsgBox_GetReadPtr, no buffer wrap around :)
        pFifoData[pFifoHeader->idxWrData] = *(iterData++);

        // If index is beyond max data, copy the value from the start of the buffer.
        if (pFifoHeader->idxWrData >= pFifoHeader->maxData)
        {
            pFifoData[pFifoHeader->idxWrData % pFifoHeader->maxData] = pFifoData[pFifoHeader->idxWrData];
        }

        // Update write index.
        pFifoHeader->idxWrData = pFifoHeader->idxWrData + 1;
    }

    // Overwrite new data write index to the current value modulo maxData
    pFifoHeader->idxWrData = pFifoHeader->idxWrData % pFifoHeader->maxData;

    // Update data and events counter
    pFifoHeader->nbData = pFifoHeader->nbData + size;
    pFifoHeader->nbEvts = pFifoHeader->nbEvts + 1;

    // Update new event field value with size and offset
    pFifoEvts[pFifoHeader->idxWrEvt].size = size;
    pFifoEvts[pFifoHeader->idxWrEvt].offset = offset;

    // Increment write event index modulo maxEvents.
    pFifoHeader->idxWrEvt = (pFifoHeader->idxWrEvt + 1) % pFifoHeader->maxEvts;

    return result;
}

static SOPC_ReturnStatus SOPC_MsgBox_ResetFifoHeader(tMsgBoxFifoHeader* pFifoHeader, //
                                                     tMsgBoxFifoEvents* pFifoEvts,   //
                                                     uint8_t* pFifoData)             //

{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    // Update data and events counter
    pFifoHeader->nbData = 0;
    pFifoHeader->nbEvts = 0;
    pFifoHeader->idxWrData = 0;
    pFifoHeader->idxWrEvt = 0;

    memset(pFifoData, 0, pFifoHeader->maxData * 2);
    memset(pFifoEvts, 0, pFifoHeader->maxEvts * sizeof(tMsgBoxFifoEvents));

    return result;
}

SOPC_MsgBox* SOPC_MsgBox_Create(
    uint32_t max_clients,  // Max message box concurrent client. Client identifier between 0 to max-1
    uint32_t max_evts,     // Max events to manage writer burst.
    uint32_t max_data_evt) // Max cumulative data in bytes.
{
    SOPC_MsgBox* pMsgBox = NULL;
    pMsgBox = SOPC_Calloc(1, sizeof(SOPC_MsgBox));
    SOPC_ReturnStatus result = SOPC_MsgBox_Initialize(pMsgBox, max_clients, max_evts, max_data_evt);
    if (result != SOPC_STATUS_OK)
    {
        SOPC_MsgBox_Destroy(&pMsgBox);
    }

    return pMsgBox;
}

void SOPC_MsgBox_Destroy(SOPC_MsgBox** ppMsgBox)
{
    if (ppMsgBox != NULL)
    {
        SOPC_MsgBox_DeInitialize(*ppMsgBox);
        SOPC_Free(*ppMsgBox);
        *ppMsgBox = NULL;
    }

    return;
}

static void SOPC_MsgBox_DeInitialize(SOPC_MsgBox* pMsgBox)
{
    if (pMsgBox != NULL)
    {
        if (pMsgBox->idxEvtReader != NULL)
        {
            SOPC_Free(pMsgBox->idxEvtReader);
            pMsgBox->idxEvtReader = NULL;
        }
        if (pMsgBox->pLockReader != NULL)
        {
            SOPC_Free(pMsgBox->pLockReader);
            pMsgBox->pLockReader = NULL;
        }

        if (pMsgBox->pFifoPublisher != NULL)
        {
            SOPC_DoubleBuffer_Destroy(&pMsgBox->pFifoPublisher);
        }

        pMsgBox->nbMaxClts = 0;
    }
}

static SOPC_ReturnStatus SOPC_MsgBox_Initialize(SOPC_MsgBox* pMsgBox,  //
                                                uint32_t max_clients,  //
                                                uint32_t max_evts,     //
                                                uint32_t max_data_evt) //
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    if (pMsgBox == NULL || max_clients < 1 || max_evts < 1 || max_data_evt < 1)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    // Set configuration : maximum concurrent clients, max events and max cumulated data

    uint64_t doubleBufferAtomicEltSize = (sizeof(tMsgBoxFifoHeader) +            // Sizeof of fifo header
                                          max_evts * sizeof(tMsgBoxFifoEvents) + // Size of event buffer
                                          max_data_evt *                         // Size of data buffer
                                              2); // Size multiplied by 2, to avoid wrap around buffer management

    // Check for overflow
    if (doubleBufferAtomicEltSize > (uint64_t) UINT32_MAX)
    {
        return SOPC_STATUS_NOK;
    }

    pMsgBox->doubleBufferFieldSize = (uint32_t) doubleBufferAtomicEltSize;
    pMsgBox->nbMaxClts = max_clients;

    // Allocation of read indexes table, one index by client. Used to detect nb events occured .
    // If this index is equal to writer index, consider 0 event.
    pMsgBox->idxEvtReader = SOPC_Calloc(1, sizeof(uint32_t) * pMsgBox->nbMaxClts);

    if (pMsgBox->idxEvtReader == NULL)
    {
        result = SOPC_STATUS_OUT_OF_MEMORY;
    }

    // Allocation of lock mechanism (table of inUse flag, one by client)
    if (result == SOPC_STATUS_OK)
    {
        pMsgBox->pLockReader = SOPC_Calloc(1, sizeof(tMsgBoxInfoSync) * pMsgBox->nbMaxClts);
        if (pMsgBox->pLockReader == NULL)
        {
            result = SOPC_STATUS_OUT_OF_MEMORY;
        }
    }

    // Allocation of double buffer used to publish FIFO image (header + events table + data buffer)
    if (result == SOPC_STATUS_OK)
    {
        pMsgBox->pFifoPublisher = SOPC_DoubleBuffer_Create(
            pMsgBox->nbMaxClts,              // Max concurrently clients
            pMsgBox->doubleBufferFieldSize); // Fifo header size + events buffer + data buffer * 2

        if (pMsgBox->pFifoPublisher == NULL)
        {
            result = SOPC_STATUS_OUT_OF_MEMORY;
        }
    }

    if (SOPC_STATUS_OK == result)
    {
        uint32_t idBuffer = UINT32_MAX;

        result = SOPC_DoubleBuffer_GetWriteBuffer(pMsgBox->pFifoPublisher, &idBuffer, NULL);

        uint32_t* pSizeField = NULL;
        uint8_t* pData = NULL;

        if (SOPC_STATUS_OK == result)
        {
            result = SOPC_DoubleBuffer_WriteBufferErase(pMsgBox->pFifoPublisher, idBuffer);
        }

        if (SOPC_STATUS_OK == result)
        {
            result = SOPC_DoubleBuffer_WriteBufferGetPtr(pMsgBox->pFifoPublisher, //
                                                         idBuffer,                //
                                                         &pData,                  //
                                                         &pSizeField,             //
                                                         true);                   //
        }

        if (result == SOPC_STATUS_OK)
        {
            tMsgBoxFifoHeader* pHeader = (void*) pData;
            pHeader->maxEvts = max_evts;
            pHeader->maxData = max_data_evt; // Real data size is multiplied by 2. maxData = real Size / 2
            pHeader->nbData = 0;
            pHeader->nbEvts = 0;
            pHeader->idxWrData = 0;
            pHeader->idxWrEvt = 0;

            *pSizeField = pMsgBox->doubleBufferFieldSize;

            result = SOPC_DoubleBuffer_ReleaseWriteBuffer(pMsgBox->pFifoPublisher, &idBuffer);
        }
    }

    // Resetting in case of error
    if (result != SOPC_STATUS_OK)
    {
        SOPC_MsgBox_DeInitialize(pMsgBox);
    }

    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_Push(SOPC_MsgBox* pMsgBox, //
                                   uint8_t* data,        //
                                   uint32_t size)        //
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    // Check invalid parameters
    if (pMsgBox == NULL || data == NULL || size < 1)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    // Try to switch flag from not use to in use
    bool expectedValue = false;
    bool desiredValue = true;
    bool bTransition = __atomic_compare_exchange(&pMsgBox->lockWriter.bIsInUse, //
                                                 &expectedValue,                //
                                                 &desiredValue,                 //
                                                 false,                         //
                                                 __ATOMIC_SEQ_CST,
                                                 __ATOMIC_SEQ_CST); //

    // If transition successful update header of the FIFO writer side, event buffer, data buffer and publish it.
    if (bTransition)
    {
        // Reserve DBO for write
        uint32_t idBuffer = UINT32_MAX;

        result = SOPC_DoubleBuffer_GetWriteBuffer(pMsgBox->pFifoPublisher, &idBuffer, NULL);

        uint8_t* pData = NULL;
        uint32_t* pDataSize = NULL;

        // Get pointer on buffer to write
        if (SOPC_STATUS_OK == result)
        {
            result = SOPC_DoubleBuffer_WriteBufferGetPtr(pMsgBox->pFifoPublisher, // DBO object
                                                         idBuffer,                // Id of reserved buffer
                                                         &pData,                  // Data out pointer
                                                         &pDataSize, // Significant bytes from previous write
                                                         false);     // Don't ignore previous data
        }

        if (result == SOPC_STATUS_OK)
        {
            tMsgBoxFifoHeader* pHeader = (void*) pData;
            tMsgBoxFifoEvents* pEvtBuffer = (void*) (pData + sizeof(tMsgBoxFifoHeader));
            uint8_t* pDataBuffer = (void*) (pData +                                        //
                                            sizeof(tMsgBoxFifoHeader) +                    //
                                            sizeof(tMsgBoxFifoEvents) * pHeader->maxEvts); //

            // FIFO header and event / data buffer update with data and size
            result = SOPC_MsgBox_UpdateFifoHeader(pHeader,     // FIFO header
                                                  pEvtBuffer,  // Event buffer
                                                  pDataBuffer, // Data buffer
                                                  data,        // Data
                                                  size);       // Data size
        }

        // Commit if no error
        if (result == SOPC_STATUS_OK)
        {
            *pDataSize = pMsgBox->doubleBufferFieldSize;

            result = SOPC_DoubleBuffer_ReleaseWriteBuffer(pMsgBox->pFifoPublisher, //
                                                          &idBuffer);              //
        }

        desiredValue = false;
        __atomic_store(&pMsgBox->lockWriter.bIsInUse, //
                       &desiredValue,                 //
                       __ATOMIC_SEQ_CST);             //
    }
    else
    {
        result = SOPC_STATUS_INVALID_STATE;
    }

    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_Reset(SOPC_MsgBox* pMsgBox)
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    // Check invalid parameters
    if (pMsgBox == NULL)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    // Try to switch flag from not use to in use
    bool expectedValue = false;
    bool desiredValue = true;
    bool bTransition = __atomic_compare_exchange(&pMsgBox->lockWriter.bIsInUse, //
                                                 &expectedValue,                //
                                                 &desiredValue,                 //
                                                 false,                         //
                                                 __ATOMIC_SEQ_CST,
                                                 __ATOMIC_SEQ_CST); //

    // If transition successful update header of the FIFO writer side, event buffer, data buffer and publish it.
    if (bTransition)
    {
        // Reserve DBO for write
        uint32_t idBuffer = UINT32_MAX;

        result = SOPC_DoubleBuffer_GetWriteBuffer(pMsgBox->pFifoPublisher, &idBuffer, NULL);

        uint8_t* pData = NULL;
        uint32_t* pDataSize = NULL;

        // Verify reservation result and get pointer on buffer
        if (SOPC_STATUS_OK == result)
        {
            result = SOPC_DoubleBuffer_WriteBufferGetPtr(pMsgBox->pFifoPublisher, //
                                                         idBuffer,                //
                                                         &pData,                  //
                                                         &pDataSize,              //
                                                         false);                  //
        }

        if (SOPC_STATUS_OK == result)
        {
            tMsgBoxFifoHeader* pHeader = (void*) pData;
            tMsgBoxFifoEvents* pEvtBuffer = (void*) (pData + sizeof(tMsgBoxFifoHeader));
            uint8_t* pDataBuffer = (void*) (pData +                                        //
                                            sizeof(tMsgBoxFifoHeader) +                    //
                                            sizeof(tMsgBoxFifoEvents) * pHeader->maxEvts); //

            // FIFO header and event / data buffer update with data and size
            result = SOPC_MsgBox_ResetFifoHeader(pHeader,      // FIFO header
                                                 pEvtBuffer,   // Event buffer
                                                 pDataBuffer); // Data buffer
        }

        // Commit if no error
        if (result == SOPC_STATUS_OK)
        {
            *pDataSize = pMsgBox->doubleBufferFieldSize;

            SOPC_DoubleBuffer_ReleaseWriteBuffer(pMsgBox->pFifoPublisher, //
                                                 &idBuffer);              //
        }

        desiredValue = false;
        __atomic_store(&pMsgBox->lockWriter.bIsInUse, //
                       &desiredValue,                 //
                       __ATOMIC_SEQ_CST);             //
    }
    else
    {
        result = SOPC_STATUS_INVALID_STATE;
    }

    return result;
}

/// @brief Message box data handle, which allow a write operation directly to event buffer.
struct SOPC_MsgBox_DataHandle
{
    SOPC_MsgBox* pMsgBox; ///< Message box handle, linked to this data handle
    uint32_t idBuffer;    ///< Buffer retrieved by SOPC_DoubleBuffer_GetWriteBuffer

    tMsgBoxFifoHeader* pHeader;     ///< Pointer on buffer where fifo header start
    tMsgBoxFifoEvents* pEvtsBuffer; ///< Pointer on buffer where event buffer start
    uint8_t* pDataToUpdate;         ///< Pointer on buffer where event data buffer start
    uint8_t* pData;                 ///< Pointer on buffer position 0, used to deal with wrap around use case.
};

SOPC_MsgBox_DataHandle* SOPC_MsgBox_DataHandle_Create(SOPC_MsgBox* pMsgBox)
{
    SOPC_MsgBox_DataHandle* p = SOPC_Calloc(1, sizeof(SOPC_MsgBox_DataHandle));

    if (NULL != p)
    {
        p->pMsgBox = pMsgBox;
        p->idBuffer = UINT32_MAX;
    }

    return p;
}

SOPC_ReturnStatus SOPC_MsgBox_DataHandle_Initialize(SOPC_MsgBox_DataHandle* pDataHandle)
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    if (NULL == pDataHandle || NULL == pDataHandle->pMsgBox || pDataHandle->idBuffer != UINT32_MAX)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    eMsgBoxInfoSync expectedStatus = E_MSG_BOX_INFO_SYNC_NOT_USED;
    eMsgBoxInfoSync desiredStatus = E_MSG_BOX_INFO_SYNC_RESERVING;
    bool bTransition = __atomic_compare_exchange(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                                                 &expectedStatus,                            //
                                                 &desiredStatus,                             //
                                                 false,                                      //
                                                 __ATOMIC_SEQ_CST,                           //
                                                 __ATOMIC_SEQ_CST);                          //

    if (bTransition)
    {
        uint8_t* pDataField = NULL;

        // Reserve buffer to write
        result = SOPC_DoubleBuffer_GetWriteBuffer(pDataHandle->pMsgBox->pFifoPublisher, //
                                                  &pDataHandle->idBuffer,               //
                                                  NULL);                                //

        // Retrieve buffer informations
        if (SOPC_STATUS_OK == result)
        {
            uint32_t* pCurrentSizeField = NULL;
            result = SOPC_DoubleBuffer_WriteBufferGetPtr(pDataHandle->pMsgBox->pFifoPublisher, //
                                                         pDataHandle->idBuffer,                //
                                                         &pDataField,                          //
                                                         &pCurrentSizeField,                   //
                                                         false);                               //
        }

        // Set shortcut pointer on header, events buffer and current free data buffer
        if (SOPC_STATUS_OK == result)
        {
            tMsgBoxFifoHeader* pHead = (void*) pDataField;
            tMsgBoxFifoEvents* pEvts = (void*) (pDataField + sizeof(tMsgBoxFifoHeader));
            uint8_t* pData =
                (void*) (pDataField + sizeof(tMsgBoxFifoHeader) + sizeof(tMsgBoxFifoEvents) * pHead->maxEvts);

            pDataHandle->pHeader = pHead;
            pDataHandle->pEvtsBuffer = pEvts;
            pDataHandle->pDataToUpdate = pData + pHead->idxWrData;
            pDataHandle->pData = pData;
        }

        // Status set to reserved if successfull
        if (SOPC_STATUS_OK != result)
        {
            pDataHandle->idBuffer = UINT32_MAX;
            pDataHandle->pHeader = NULL;
            pDataHandle->pDataToUpdate = NULL;
            pDataHandle->pData = NULL;
            pDataHandle->pEvtsBuffer = NULL;
            desiredStatus = E_MSG_BOX_INFO_SYNC_NOT_USED;
            __atomic_store(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                           &desiredStatus,                             //
                           __ATOMIC_SEQ_CST);                          //
        }
        else
        {
            desiredStatus = E_MSG_BOX_INFO_SYNC_RESERVED;
            __atomic_store(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                           &desiredStatus,                             //
                           __ATOMIC_SEQ_CST);                          //
        }
    }
    else
    {
        return SOPC_STATUS_INVALID_STATE;
    }

    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_DataHandle_GetDataEvt(SOPC_MsgBox_DataHandle* pDataHandle, //
                                                    uint8_t** ppData,                    //
                                                    uint32_t* pMaxAllowedSize)           //
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    if (NULL == pDataHandle || NULL == pDataHandle->pDataToUpdate || NULL == pDataHandle->pData ||
        NULL == pDataHandle->pEvtsBuffer || NULL == pDataHandle->pHeader || UINT32_MAX == pDataHandle->idBuffer ||
        NULL == pDataHandle->pMsgBox)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    eMsgBoxInfoSync expectedValue = E_MSG_BOX_INFO_SYNC_RESERVED;
    eMsgBoxInfoSync desiredValue = E_MSG_BOX_INFO_SYNC_RESERVED_USED;
    bool bTransition = __atomic_compare_exchange(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                                                 &expectedValue,                             //
                                                 &desiredValue,                              //
                                                 false,                                      //
                                                 __ATOMIC_SEQ_CST,                           //
                                                 __ATOMIC_SEQ_CST);                          //

    if (bTransition)
    {
        *ppData = pDataHandle->pDataToUpdate;
        *pMaxAllowedSize = pDataHandle->pHeader->maxData;

        desiredValue = E_MSG_BOX_INFO_SYNC_RESERVED;
        __atomic_store(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                       &desiredValue,                              //
                       __ATOMIC_SEQ_CST);                          //
    }
    else
    {
        result = SOPC_STATUS_INVALID_STATE;
    }

    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_DataHandle_UpdateDataEvtSize(SOPC_MsgBox_DataHandle* pDataHandle, //
                                                           uint32_t size)                       //
{
    if (NULL == pDataHandle || NULL == pDataHandle->pDataToUpdate || NULL == pDataHandle->pData ||
        NULL == pDataHandle->pEvtsBuffer || NULL == pDataHandle->pHeader || UINT32_MAX == pDataHandle->idBuffer ||
        NULL == pDataHandle->pMsgBox)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    eMsgBoxInfoSync expectedStatus = E_MSG_BOX_INFO_SYNC_RESERVED;
    eMsgBoxInfoSync desiredStatus = E_MSG_BOX_INFO_SYNC_RESERVED_USED;
    bool bTransition = __atomic_compare_exchange(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                                                 &expectedStatus,                            //
                                                 &desiredStatus,                             //
                                                 false,                                      //
                                                 __ATOMIC_SEQ_CST,                           //
                                                 __ATOMIC_SEQ_CST);                          //

    if (bTransition)
    {
        if ((size > pDataHandle->pHeader->maxData) || (size < 1))
        {
            result = SOPC_STATUS_NOK;
        }

        // Delete records if not enough space (at least one event with enough free data size)
        if (SOPC_STATUS_OK == result)
        {
            uint32_t iterEvent = pDataHandle->pHeader->idxWrEvt;
            uint32_t nextSize = 0;
            while (((pDataHandle->pHeader->nbData + size) > pDataHandle->pHeader->maxData) &&
                   ((pDataHandle->pHeader->nbEvts + 1) > pDataHandle->pHeader->maxEvts))
            {
                nextSize = pDataHandle->pEvtsBuffer[iterEvent].size;
                // Delete record informations
                if (nextSize > 0)
                {
                    pDataHandle->pEvtsBuffer[iterEvent].offset = 0;
                    pDataHandle->pEvtsBuffer[iterEvent].size = 0;
                    pDataHandle->pHeader->nbData -= nextSize;
                    pDataHandle->pHeader->nbEvts -= 1;
                }
                iterEvent = (iterEvent + 1) % pDataHandle->pHeader->maxEvts;
            }
        }

        // Update record
        if (SOPC_STATUS_OK == result)
        {
            // Offset of record is saved, used to duplicate data to conserved linear buffer
            uint32_t offset = pDataHandle->pHeader->idxWrData;
            // Update event record information with data write index before update this one
            // Update event record information with new data size
            pDataHandle->pEvtsBuffer[pDataHandle->pHeader->idxWrEvt].offset = pDataHandle->pHeader->idxWrData;
            pDataHandle->pEvtsBuffer[pDataHandle->pHeader->idxWrEvt].size = size;

            // Update write event index and write data index
            pDataHandle->pHeader->idxWrEvt = (pDataHandle->pHeader->idxWrEvt + 1) % pDataHandle->pHeader->maxEvts;
            pDataHandle->pHeader->idxWrData = (pDataHandle->pHeader->idxWrData + size) % pDataHandle->pHeader->maxData;

            // Update event and data counter
            pDataHandle->pHeader->nbEvts++;
            pDataHandle->pHeader->nbData += size;

            // If wrap around, calculate overhead size and copy it from offset 0 to overhead size.
            if ((size + offset) >= pDataHandle->pHeader->maxData)
            {
                uint32_t sizeToDup = size - (pDataHandle->pHeader->maxData - offset);

                for (uint32_t i = 0; i < sizeToDup; i++)
                {
                    pDataHandle->pData[i] = pDataHandle->pData[pDataHandle->pHeader->maxData + i];
                }
            }
        }

        desiredStatus = E_MSG_BOX_INFO_SYNC_RESERVED;
        __atomic_store(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                       &desiredStatus,                             //
                       __ATOMIC_SEQ_CST);                          //
    }
    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_DataHandle_Finalize(SOPC_MsgBox_DataHandle* pDataHandle, //
                                                  bool bCancel)                        //
{
    if (NULL == pDataHandle || NULL == pDataHandle->pDataToUpdate || NULL == pDataHandle->pData ||
        NULL == pDataHandle->pEvtsBuffer || NULL == pDataHandle->pHeader || UINT32_MAX == pDataHandle->idBuffer ||
        NULL == pDataHandle->pMsgBox)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    eMsgBoxInfoSync expectedStatus = E_MSG_BOX_INFO_SYNC_RESERVED;
    eMsgBoxInfoSync desiredStatus = E_MSG_BOX_INFO_SYNC_RELEASING;
    bool bTransition = __atomic_compare_exchange(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                                                 &expectedStatus,                            //
                                                 &desiredStatus,                             //
                                                 false,                                      //
                                                 __ATOMIC_SEQ_CST,                           //
                                                 __ATOMIC_SEQ_CST);                          //

    if (bTransition)
    {
        if (SOPC_STATUS_OK == result && !bCancel)
        {
            result = SOPC_DoubleBuffer_ReleaseWriteBuffer(pDataHandle->pMsgBox->pFifoPublisher, &pDataHandle->idBuffer);
        }

        pDataHandle->idBuffer = UINT32_MAX;
        pDataHandle->pHeader = NULL;
        pDataHandle->pDataToUpdate = NULL;
        pDataHandle->pData = NULL;
        pDataHandle->pEvtsBuffer = NULL;

        desiredStatus = E_MSG_BOX_INFO_SYNC_NOT_USED;
        __atomic_store(&pDataHandle->pMsgBox->lockWriter.eIsInUse, //
                       &desiredStatus,                             //
                       __ATOMIC_SEQ_CST);                          //
    }
    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_DataHandle_Destroy(SOPC_MsgBox_DataHandle** ppDataHandle)
{
    if (ppDataHandle == NULL)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    SOPC_ReturnStatus result = SOPC_STATUS_INVALID_PARAMETERS;
    SOPC_MsgBox_DataHandle* pDataHandle = *ppDataHandle;
    if (NULL != pDataHandle)
    {
        if (pDataHandle->idBuffer == UINT32_MAX)
        {
            SOPC_Free(pDataHandle);
            *ppDataHandle = NULL;
            result = SOPC_STATUS_OK;
        }
        else
        {
            result = SOPC_STATUS_INVALID_STATE;
        }
    }
    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_Pop_Initialize(SOPC_MsgBox* pMsgBox, //
                                             uint32_t* pIdBuffer)  //
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    if (NULL == pMsgBox || NULL == pIdBuffer)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }
    result = SOPC_DoubleBuffer_GetReadBuffer(pMsgBox->pFifoPublisher, pIdBuffer);
    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_Pop_GetEvtPtr(SOPC_MsgBox* pMsgBox,            //
                                            uint32_t idBuffer,               //
                                            uint32_t idclient,               //
                                            uint8_t** ppData,                //
                                            uint32_t* pSize,                 //
                                            uint32_t* pNbPendOrIgnoreEvents, //
                                            SOPC_MsgBox_Mode mode)           //
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    if (NULL == pMsgBox || UINT32_MAX == idBuffer || idclient >= pMsgBox->nbMaxClts || ppData == NULL ||
        pSize == NULL || pNbPendOrIgnoreEvents == NULL)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    uint8_t* pData = NULL;
    uint32_t dataSize = 0;
    uint32_t nbPendingEvents = 0;

    bool expectedValue = false;
    bool desiredValue = true;
    bool bTransition = __atomic_compare_exchange(&pMsgBox->pLockReader[idclient].bIsInUse, //
                                                 &expectedValue,                           //
                                                 &desiredValue,                            //
                                                 false,                                    //
                                                 __ATOMIC_SEQ_CST,                         //
                                                 __ATOMIC_SEQ_CST);                        //

    if (bTransition)
    {
        tMsgBoxFifoHeader* pHeader = NULL;
        uint32_t nbEventsFromCltView = 0;

        // Get FIFO data pointer
        uint32_t size = 0;

        result = SOPC_DoubleBuffer_ReadBufferPtr(pMsgBox->pFifoPublisher, // DBO object
                                                 idBuffer,                // Id returned by Pop_Initalized
                                                 (uint8_t**) &pHeader,    // FIFO header image pointer
                                                 &size);                  // size can be read

        // Check valid minimum size
        // Check if at least 1 event exist. If it exist, at least one event with a dataSize > 0 exist.
        if (result != SOPC_STATUS_OK || pHeader->nbEvts <= 0 || size < pMsgBox->doubleBufferFieldSize)
        {
            // No event in the DBO or DBO reset. Reset reader index.
            pMsgBox->idxEvtReader[idclient] = 0;
            pData = NULL;
            dataSize = 0;
            nbPendingEvents = 0;
        }
        else
        {
            // Check for new events. If read index and write index are equals, overflow. 0 events are counted.
            // If you want to get last without overflow and no event, use GET_LAST mode.

            if (pMsgBox->idxEvtReader[idclient] > pHeader->idxWrEvt)
            {
                nbEventsFromCltView = pHeader->idxWrEvt + pHeader->maxEvts - pMsgBox->idxEvtReader[idclient];
            }
            else
            {
                nbEventsFromCltView = pHeader->idxWrEvt - pMsgBox->idxEvtReader[idclient];
            }

            // If no event, return no data except for GET_LAST mode.
            // GET LAST mode ignore 0 event from reader point of view.
            if (((nbEventsFromCltView > 0) || (mode == SOPC_MSGBOX_MODE_GET_LAST)))
            {
                // Loop until a valid data is reached
                // This condition is guaranteed by update policy writer point of view
                while (pData == NULL)
                {
                    // Get client event read index
                    uint32_t cltEvtIdx = 0;

                    // If mode GET_NEW_LAST or GET_LAST, double buffer write index is used instead of
                    // reader index. pData is never NULL because dataSize > 0.
                    if (mode >= SOPC_MSGBOX_MODE_GET_NEW_LAST)
                    {
                        cltEvtIdx = (pHeader->idxWrEvt + pHeader->maxEvts - 1) % pHeader->maxEvts;
                    }
                    else
                    {
                        cltEvtIdx = pMsgBox->idxEvtReader[idclient];
                    }

                    // Get event pointed by index
                    tMsgBoxFifoEvents* pEvts = (void*) ((uint8_t*) pHeader +                    //
                                                        sizeof(tMsgBoxFifoHeader) +             //
                                                        cltEvtIdx * sizeof(tMsgBoxFifoEvents)); //

                    // Get data offset
                    uint32_t dataOffset = pEvts->offset;

                    // Get event data size
                    dataSize = pEvts->size;

                    // Treat the case of an overflow or if this event has been removed to liberate data zone
                    if (dataSize > 0)
                    {
                        // Get pointer on data
                        pData = ((uint8_t*) pHeader +                           //
                                 sizeof(tMsgBoxFifoHeader) +                    //
                                 pHeader->maxEvts * sizeof(tMsgBoxFifoEvents) + //
                                 dataOffset);                                   //
                    }

                    // Update index for this client
                    if (mode >= SOPC_MSGBOX_MODE_GET_NEW_LAST)
                    {
                        pMsgBox->idxEvtReader[idclient] = pHeader->idxWrEvt;
                    }
                    else
                    {
                        pMsgBox->idxEvtReader[idclient] = (pMsgBox->idxEvtReader[idclient] + 1) % pHeader->maxEvts;
                    }

                    // Pending or not read events. Can be 0 in the case of GET_LAST mode.
                    nbPendingEvents = nbEventsFromCltView > 0 ? nbEventsFromCltView - 1 : 0;

                    // Update nbEvents used by nbPendingEvents field.
                    if (pMsgBox->idxEvtReader[idclient] > pHeader->idxWrEvt)
                    {
                        nbEventsFromCltView = pHeader->idxWrEvt + pHeader->maxEvts - pMsgBox->idxEvtReader[idclient];
                    }
                    else
                    {
                        nbEventsFromCltView = pHeader->idxWrEvt - pMsgBox->idxEvtReader[idclient];
                    }
                }
            }
            else
            {
                // No event reader point of view and mode is NORMAL or GET_NEW_LAST
                pData = NULL;
                dataSize = 0;
                nbPendingEvents = 0;
            }
        }

        // Mark API as not in use.
        desiredValue = false;
        __atomic_store(&pMsgBox->pLockReader[idclient].bIsInUse, //
                       &desiredValue,                            //
                       __ATOMIC_SEQ_CST);                        //
    }
    else
    {
        result = SOPC_STATUS_INVALID_STATE;
    }

    // Output results.
    *ppData = pData;
    *pSize = dataSize;
    *pNbPendOrIgnoreEvents = nbPendingEvents;
    return result;
}

SOPC_ReturnStatus SOPC_MsgBox_Pop_Finalize(SOPC_MsgBox* pMsgBox, //
                                           uint32_t* pIdBuffer)  //
{
    SOPC_ReturnStatus result = SOPC_STATUS_OK;

    if (NULL == pMsgBox || pIdBuffer == NULL)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }
    result = SOPC_DoubleBuffer_ReleaseReadBuffer(pMsgBox->pFifoPublisher, pIdBuffer);
    return result;
}
