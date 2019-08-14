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

#include "p_analyzer.h"

typedef enum E_ANALYZER_EVENT
{
    ANALYZER_EVENT_BYTE,
    ANALYZER_EVENT_DELIM,
    ANALYZER_EVENT_TIMEOUT,
    ANALYZER_EVENT_MAX,
    ANALYZER_EVENT_SIZEOF = UINT32_MAX
} eAnalyzerEvent;

typedef eAnalyzerStatus (*ptrCbAnalyzer)(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);

static eAnalyzerStatus cbFsmReceiveSOF(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveTAG(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveLNG(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveDAT(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveCRC(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveEOF(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveNOP(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveDLM(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);
static eAnalyzerStatus cbFsmReceiveTMO(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value);

static uint16_t UpdateChecksum(uint16_t reminder, uint8_t value);

static ptrCbAnalyzer tabAnalyzerFsm[ANALYZER_STATUS_MAX][ANALYZER_EVENT_MAX] = {
    /*                                          EVENT_BYTE       EVENT_DLM        EVENT_TMO*/

    /*ANALYZER_STATUS_WAIT_FOR_SOF          */ {cbFsmReceiveSOF, cbFsmReceiveNOP, cbFsmReceiveNOP},
    /*ANALYZER_STATUS_WAIT_FOR_TAG          */ {cbFsmReceiveTAG, cbFsmReceiveDLM, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_DELIM_TAG    */ {cbFsmReceiveTAG, cbFsmReceiveTAG, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_LENGTH       */ {cbFsmReceiveLNG, cbFsmReceiveDLM, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_DELIM_LENGTH */ {cbFsmReceiveLNG, cbFsmReceiveLNG, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_DATA         */ {cbFsmReceiveDAT, cbFsmReceiveDLM, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_DELIM_DATA   */ {cbFsmReceiveDAT, cbFsmReceiveDAT, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_CRC          */ {cbFsmReceiveCRC, cbFsmReceiveDLM, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_DELIM_CRC    */ {cbFsmReceiveCRC, cbFsmReceiveCRC, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_WAIT_FOR_EOF          */ {cbFsmReceiveEOF, cbFsmReceiveEOF, cbFsmReceiveTMO},
    /*ANALYZER_STATUS_READY                 */ {cbFsmReceiveSOF, cbFsmReceiveNOP, cbFsmReceiveNOP}

};

static eAnalyzerStatus cbFsmReceiveTMO(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;

    if (pCtx->trigTmoCpt > 0)
    {
        pCtx->cptTimeout++;
        if ((pCtx->cptTimeout >= pCtx->trigTmoCpt))
        {
            pCtx->status = ANALYZER_STATUS_WAIT_FOR_SOF;
            status = pCtx->status;
        }
    }

    return status;
}

static eAnalyzerStatus cbFsmReceiveNOP(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    return pCtx->status;
}

static eAnalyzerStatus cbFsmReceiveSOF(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;

    if (value == PLT_SOF)
    {
        memset(&pCtx->currentMsg, 0, sizeof(tAnalyzerMsg));
        pCtx->computedCrc = 0;
        pCtx->receivedCrc = 0;
        pCtx->cptTimeout = 0;
        pCtx->currentFieldLength = 0;
        pCtx->cptTimeout = 0;
        pCtx->status = ANALYZER_STATUS_WAIT_FOR_TAG;
        status = pCtx->status;
    }

    return status;
}

static eAnalyzerStatus cbFsmReceiveTAG(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;

    if (status == ANALYZER_STATUS_WAIT_FOR_DELIM_TAG)
    {
        value = value & PLT_MASK_DELIM_OFF;
    }

    pCtx->currentMsg.tag = value;
    pCtx->computedCrc = UpdateChecksum(pCtx->computedCrc, value);
    pCtx->currentFieldLength = 0;
    pCtx->status = ANALYZER_STATUS_WAIT_FOR_LENGTH;
    status = pCtx->status;

    return status;
}

static eAnalyzerStatus cbFsmReceiveLNG(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;
    uint16_t currentValue = 0;

    if (status == ANALYZER_STATUS_WAIT_FOR_DELIM_LENGTH)
    {
        value = value & PLT_MASK_DELIM_OFF;
    }

    currentValue = value;

    pCtx->computedCrc = UpdateChecksum(pCtx->computedCrc, value);

    pCtx->currentFieldLength++;

    pCtx->currentMsg.length += currentValue
                               << (LNG_REAL_BITS_LENGTH - LNG_BITS_PER_TRANSPORT_BYTE * pCtx->currentFieldLength);

    if (pCtx->currentFieldLength >= LNG_NB_TRANSPORT_BYTES)
    {
        if (pCtx->currentMsg.length > PLT_MAX_LENGTH)
        {
            pCtx->status = ANALYZER_STATUS_WAIT_FOR_SOF;
        }
        else
        {
            pCtx->currentFieldLength = 0;
            pCtx->status = ANALYZER_STATUS_WAIT_FOR_DATA;
        }
        status = pCtx->status;
    }

    return status;
}

static eAnalyzerStatus cbFsmReceiveDAT(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;

    if (status == ANALYZER_STATUS_WAIT_FOR_DELIM_DATA)
    {
        value = value & PLT_MASK_DELIM_OFF;
    }

    pCtx->computedCrc = UpdateChecksum(pCtx->computedCrc, value);

    pCtx->currentMsg.data[pCtx->currentFieldLength] = value;

    pCtx->currentFieldLength++;

    if (pCtx->currentFieldLength >= pCtx->currentMsg.length)
    {
        pCtx->currentFieldLength = 0;
        pCtx->status = ANALYZER_STATUS_WAIT_FOR_CRC;
        status = pCtx->status;
    }

    return status;
}

static eAnalyzerStatus cbFsmReceiveCRC(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;
    uint16_t currentValue = 0;

    if (status == ANALYZER_STATUS_WAIT_FOR_DELIM_CRC)
    {
        value = value & PLT_MASK_DELIM_OFF;
    }

    currentValue = value;

    pCtx->currentFieldLength++;

    pCtx->receivedCrc =
        pCtx->receivedCrc +
        (currentValue << (CRC_REAL_BITS_LENGTH - CRC_BITS_PER_TRANSPORT_BYTE * pCtx->currentFieldLength));

    if (pCtx->currentFieldLength >= CRC_NB_TRANSPORT_BYTES)
    {
        if (pCtx->receivedCrc == pCtx->computedCrc)
        {
            pCtx->currentFieldLength = 0;
            pCtx->status = ANALYZER_STATUS_WAIT_FOR_EOF;
        }
        else
        {
            pCtx->status = ANALYZER_STATUS_WAIT_FOR_SOF;
        }

        status = pCtx->status;
    }

    return status;
}

static eAnalyzerStatus cbFsmReceiveEOF(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;

    if (value == PLT_EOF)
    {
        pCtx->status = ANALYZER_STATUS_READY;
    }
    else
    {
        pCtx->status = ANALYZER_STATUS_WAIT_FOR_SOF;
    }

    status = pCtx->status;

    return status;
}

static eAnalyzerStatus cbFsmReceiveDLM(tAnalyzerWks* pCtx, eAnalyzerEvent event, uint8_t value)
{
    eAnalyzerStatus status = pCtx->status;
    switch (status)
    {
    case ANALYZER_STATUS_WAIT_FOR_TAG:
        pCtx->status = ANALYZER_STATUS_WAIT_FOR_DELIM_TAG;
        break;
    case ANALYZER_STATUS_WAIT_FOR_LENGTH:
        pCtx->status = ANALYZER_STATUS_WAIT_FOR_DELIM_LENGTH;
        break;
    case ANALYZER_STATUS_WAIT_FOR_DATA:
        pCtx->status = ANALYZER_STATUS_WAIT_FOR_DELIM_DATA;
        break;
    case ANALYZER_STATUS_WAIT_FOR_CRC:
        pCtx->status = ANALYZER_STATUS_WAIT_FOR_DELIM_CRC;
        break;
    default:
        break;
    }

    status = pCtx->status;
    return status;
}

eAnalyzerStatus UpdateAnalyzerTmo(tAnalyzerWks* pCtx)
{
    if (pCtx == NULL)
    {
        return ANALYZER_STATUS_WAIT_FOR_SOF;
    }

    return tabAnalyzerFsm[pCtx->status][ANALYZER_EVENT_TIMEOUT](pCtx, ANALYZER_EVENT_TIMEOUT, 0);
}

eAnalyzerStatus ExecuteAnalyzer(tAnalyzerWks* pCtx, uint8_t value)
{
    eAnalyzerStatus status = ANALYZER_STATUS_WAIT_FOR_SOF;
    if (pCtx == NULL)
    {
        return ANALYZER_STATUS_WAIT_FOR_SOF;
    }

    switch (value)
    {
    case PLT_DLM:
    {
        status = tabAnalyzerFsm[pCtx->status][ANALYZER_EVENT_DELIM](pCtx,                 //
                                                                    ANALYZER_EVENT_DELIM, //
                                                                    value);               //
    }
    break;
    default:
    {
        status = tabAnalyzerFsm[pCtx->status][ANALYZER_EVENT_BYTE](pCtx,                //
                                                                   ANALYZER_EVENT_BYTE, //
                                                                   value);              //
    }
    break;
    }
    return status;
}

tAnalyzerMsg* GetReadyMessage(tAnalyzerWks* pCtx)
{
    if (pCtx == NULL || pCtx->status != ANALYZER_STATUS_READY)
    {
        return NULL;
    }
    return &pCtx->currentMsg;
}

eAnalyzerResult InitializeAnalyzer(tAnalyzerWks* pCtx, uint16_t trigTmoCpt)
{
    if (pCtx == NULL)
    {
        return ANALYZER_RESULT_NOK;
    }

    memset(pCtx, 0, sizeof(tAnalyzerWks));

    pCtx->trigTmoCpt = trigTmoCpt;

    return ANALYZER_RESULT_OK;
}

void DeinitializeAnalyzer(tAnalyzerWks* pCtx)
{
    if (pCtx != NULL)
    {
        memset(pCtx, 0, sizeof(tAnalyzerWks));
    }
}

tAnalyzerWks* CreateAnalyzer(uint16_t trigTmoCpt)
{
    tAnalyzerWks* p = pvPortMalloc(sizeof(tAnalyzerWks));
    if (p != NULL)
    {
        eAnalyzerResult res = InitializeAnalyzer(p, trigTmoCpt);
        if (res != ANALYZER_RESULT_OK)
        {
            vPortFree(p);
        }
    }
    return p;
}

void DestroyAnalyzer(tAnalyzerWks** ppCtx)
{
    if ((ppCtx != NULL) && ((*ppCtx) != NULL))
    {
        DeinitializeAnalyzer(*ppCtx);
        memset(*ppCtx, 0, sizeof(tAnalyzerWks));
        vPortFree(*ppCtx);
        *ppCtx = NULL;
    }
}

uint16_t BuildFrame(uint8_t tag,
                    uint16_t in_length,
                    const uint8_t* pInValue,
                    uint16_t max_out_length,
                    uint8_t* pOutValue)
{
    uint8_t length_MSB = (in_length >> 8) & 0xFF;
    uint8_t length_LSB = in_length & 0xFF;
    uint8_t crc_MSB = 0;
    uint8_t crc_LSB = 0;
    uint16_t crc = 0;
    uint16_t wIter = 0;
    uint16_t wJter = 0;

    if (in_length > PLT_MAX_LENGTH || pInValue == NULL || pOutValue == NULL || max_out_length < PLT_MAX_FRAME_SIZE)
    {
        return 0;
    }

    memset(pOutValue, 0, max_out_length);

    pOutValue[wIter++] = PLT_SOF;

    if (tag == PLT_DLM || tag == PLT_SOF || tag == PLT_EOF)
    {
        pOutValue[wIter++] = PLT_DLM;
        pOutValue[wIter++] = tag | PLT_MASK_DELIM_ON;
    }
    else
    {
        pOutValue[wIter++] = tag;
    }
    crc = UpdateChecksum(crc, tag);

    if (length_MSB == PLT_DLM || length_MSB == PLT_SOF || length_MSB == PLT_EOF)
    {
        pOutValue[wIter++] = PLT_DLM;
        pOutValue[wIter++] = length_MSB | PLT_MASK_DELIM_ON;
    }
    else
    {
        pOutValue[wIter++] = length_MSB;
    }
    crc = UpdateChecksum(crc, length_MSB);

    if (length_LSB == PLT_DLM || length_LSB == PLT_SOF || length_LSB == PLT_EOF)
    {
        pOutValue[wIter++] = PLT_DLM;
        pOutValue[wIter++] = length_LSB | PLT_MASK_DELIM_ON;
    }
    else
    {
        pOutValue[wIter++] = length_LSB;
    }
    crc = UpdateChecksum(crc, length_LSB);

    for (wJter = 0; wJter < in_length; wJter++)
    {
        if (pInValue[wJter] == PLT_DLM || pInValue[wJter] == PLT_SOF || pInValue[wJter] == PLT_EOF)
        {
            pOutValue[wIter++] = PLT_DLM;
            pOutValue[wIter++] = pInValue[wJter] | PLT_MASK_DELIM_ON;
        }
        else
        {
            pOutValue[wIter++] = pInValue[wJter];
        }
        crc = UpdateChecksum(crc, pInValue[wJter]);
    }

    crc_MSB = (crc >> 8) & 0xFF;
    crc_LSB = crc & 0xFF;

    if (crc_MSB == PLT_DLM || crc_MSB == PLT_SOF || crc_MSB == PLT_EOF)
    {
        pOutValue[wIter++] = PLT_DLM;
        pOutValue[wIter++] = crc_MSB | PLT_MASK_DELIM_ON;
    }
    else
    {
        pOutValue[wIter++] = crc_MSB;
    }

    if (length_LSB == crc_LSB || crc_LSB == PLT_SOF || crc_LSB == PLT_EOF)
    {
        pOutValue[wIter++] = PLT_DLM;
        pOutValue[wIter++] = crc_LSB | PLT_MASK_DELIM_ON;
    }
    else
    {
        pOutValue[wIter++] = crc_LSB;
    }

    pOutValue[wIter++] = PLT_EOF;

    return wIter;
}

static uint16_t UpdateChecksum(uint16_t reminder, uint8_t value)
{
    const uint16_t carryMask = (uint16_t) 0x8000;
    const uint16_t poly = (uint16_t) PLT_POLY;
    uint16_t wIter = 0;
    uint16_t result = reminder;
    uint16_t currentValue = value;

    result = result ^ (currentValue << 8);

    for (wIter = 0; wIter < 8; wIter++)
    {
        if ((carryMask & result) == 0)
        {
            result = result << 1;
        }
        else
        {
            result = (result << 1) ^ poly;
        }
    }

    return result;
}
