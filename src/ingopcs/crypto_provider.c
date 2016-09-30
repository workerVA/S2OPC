/*
 * Defines the cryptographic providers: structure r/w data alongside a read-only cryptoprofile.
 *
 *  Created on: Sep 28, 2016
 *      Author: PAB
 */


#include <stdlib.h>
#include <string.h>

#include "ua_builtintypes.h"
#include "crypto_provider.h"
#include "crypto_profiles.h"


CryptoProvider *CryptoProvider_Create_Low(const char *uri)
{
    CryptoProvider *pCryptoProvider = UA_NULL;
    const CryptoProfile *pProfile = UA_NULL;

    pProfile = CryptoProfile_Get(uri);
    if(UA_NULL != pProfile)
    {
        pCryptoProvider = (CryptoProvider *)malloc(sizeof(CryptoProvider));
        if(UA_NULL != pCryptoProvider)
        {
            *(const CryptoProfile **)(&pCryptoProvider->pProfile) = pProfile; // TODO: this is a side-effect of putting too much const
            if(STATUS_OK != CryptoProvider_LibInit(pCryptoProvider))
            {
                free(pCryptoProvider);
                pCryptoProvider = UA_NULL;
            }
        }
    }

    return pCryptoProvider;
}


void CryptoProvider_Delete_Low(CryptoProvider* pCryptoProvider)
{
    if(UA_NULL != pCryptoProvider)
    {
        CryptoProvider_LibDeinit(pCryptoProvider);
        free(pCryptoProvider);
    }
}


StatusCode CryptoProvider_SymmetricEncrypt_Low(const CryptoProvider *pProvider,
                                               const uint8_t *pInput,
                                               uint32_t lenPlainText,
                                               const KeyBuffer *pKey,
                                               const uint8_t *pIV,
                                               uint8_t *pOutput,
                                               uint32_t lenOutput)
{
    if(UA_NULL == pProvider || UA_NULL == pProvider->pProfile || UA_NULL == pInput || UA_NULL == pKey || UA_NULL == pIV || UA_NULL == pOutput)
        return STATUS_INVALID_PARAMETERS;

    return pProvider->pProfile->pFnSymmEncrypt(pProvider, pInput, lenPlainText, pKey, pIV, pOutput, lenOutput);
}


StatusCode CryptoProvider_SymmetricDecrypt_Low(const CryptoProvider *pProvider,
                                               const uint8_t *pInput,
                                               uint32_t lenCipherText,
                                               const KeyBuffer *pKey,
                                               const uint8_t *pIV,
                                               uint8_t *pOutput,
                                               uint32_t lenOutput)
{
    if(UA_NULL == pProvider || UA_NULL == pProvider->pProfile || UA_NULL == pInput || UA_NULL == pKey || UA_NULL == pIV || UA_NULL == pOutput)
        return STATUS_INVALID_PARAMETERS;

    return pProvider->pProfile->pFnSymmDecrypt(pProvider, pInput, lenCipherText, pKey, pIV, pOutput, lenOutput);
}


StatusCode CryptoProvider_Symmetric_GetKeyLength_Low(const CryptoProvider *pProvider,
                                                     uint32_t *length)
{
    if(UA_NULL == pProvider || UA_NULL == pProvider->pProfile || UA_NULL == length)
        return STATUS_INVALID_PARAMETERS;

    switch(pProvider->pProfile->SecurityPolicyID)
    {
    case SecurityPolicy_Invalid_ID:
    default:
        return STATUS_NOK;
    case SecurityPolicy_Basic256Sha256_ID:
        *length = SecurityPolicy_Basic256Sha256_Symm_KeyLength;
        break;
    }

    return STATUS_OK;
}


StatusCode CryptoProvider_Symmetric_GetOutputLength_Low(const CryptoProvider *pProvider,
                                                        uint32_t lengthIn,
                                                        uint32_t *pLengthOut)
{
    if(UA_NULL == pLengthOut)
        return STATUS_INVALID_PARAMETERS;

    *pLengthOut = lengthIn;

    return STATUS_OK;
}


// pLenOutput can be UA_NULL
StatusCode CryptoProvider_SymmetricSign_Low(const CryptoProvider *pProvider,
                                            const uint8_t *pInput,
                                            uint32_t lenInput,
                                            const uint8_t *pKey,
                                            uint8_t *pOutput,
                                            uint32_t *pLenOutput)
{
    if(UA_NULL == pProvider || UA_NULL == pProvider->pProfile || UA_NULL == pInput || UA_NULL == pKey || UA_NULL == pOutput)
        return STATUS_INVALID_PARAMETERS;

    if(UA_NULL != pLenOutput)
        CryptoProvider_SymmetricSignature_GetLength_Low(pProvider, pLenOutput);

    return pProvider->pProfile->pFnSymmSign(pProvider, pInput, lenInput, pKey, pOutput);
}


StatusCode CryptoProvider_SymmetricVerify_Low(const CryptoProvider *pProvider,
                                              const uint8_t *pInput,
                                              uint32_t lenInput,
                                              const uint8_t *pKey,
                                              const uint8_t *pSignature)
{
    if(UA_NULL == pProvider || UA_NULL == pProvider->pProfile || UA_NULL == pInput || UA_NULL == pKey || UA_NULL == pSignature)
        return STATUS_INVALID_PARAMETERS;

    return pProvider->pProfile->pFnSymmVerif(pProvider, pInput, lenInput, pKey, pSignature);
}


StatusCode CryptoProvider_SymmetricSignature_GetLength_Low(const CryptoProvider *pProvider,
                                                           uint32_t *pLength)
{
    if(UA_NULL == pProvider || UA_NULL == pProvider->pProfile || UA_NULL == pLength)
        return STATUS_INVALID_PARAMETERS;

    switch(pProvider->pProfile->SecurityPolicyID)
    {
    case SecurityPolicy_Invalid_ID:
    default:
        return STATUS_NOK;
    case SecurityPolicy_Basic256Sha256_ID:
        *pLength = SecurityPolicy_Basic256Sha256_Symm_SignatureLength;
        break;
    }

    return STATUS_OK;
}


StatusCode CryptoProvider_SymmetricGenerateKey_Low(const CryptoProvider *pProvider,
                                                   uint8_t *pKey)
{
    if(UA_NULL == pProvider || UA_NULL == pProvider->pProfile || UA_NULL == pProvider->pCryptolibContext || UA_NULL == pKey)
        return STATUS_INVALID_PARAMETERS;

    return pProvider->pProfile->pFnSymmGenKey(pProvider, pKey);
}
