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

/*------------------------
   Exported Declarations
  ------------------------*/
#include <assert.h>
#include <inttypes.h>
#include <string.h>

#include "msg_session_bs.h"
#include "util_b2c.h"

#include "sopc_logger.h"
#include "sopc_toolkit_config_internal.h"
#include "util_discovery_services.h"

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void msg_session_bs__INITIALISATION(void) {}

/*--------------------
   OPERATIONS Clause
  --------------------*/

void msg_session_bs__write_activate_msg_user(const constants__t_msg_i msg_session_bs__msg,
                                             const constants__t_user_token_i msg_session_bs__p_user_token)
{
    OpcUa_ActivateSessionRequest* req = (OpcUa_ActivateSessionRequest*) msg_session_bs__msg;

    SOPC_ReturnStatus status = SOPC_ExtensionObject_Copy(&req->UserIdentityToken, msg_session_bs__p_user_token);
    if (SOPC_STATUS_OK != status)
    {
        SOPC_Logger_TraceError("message_out_bs__write_activate_msg_user: userToken copy failed");
        assert(false);
    }
}

void msg_session_bs__write_create_session_req_msg_endpointUrl(
    const constants__t_msg_i msg_session_bs__msg,
    const constants__t_channel_config_idx_i msg_session_bs__channel_config_idx)
{
    SOPC_ReturnStatus status = SOPC_STATUS_NOK;
    OpcUa_CreateSessionRequest* createSessionReq = (OpcUa_CreateSessionRequest*) msg_session_bs__msg;
    SOPC_SecureChannel_Config* chConfig = SOPC_ToolkitClient_GetSecureChannelConfig(msg_session_bs__channel_config_idx);
    if (NULL != chConfig)
    {
        status = SOPC_String_CopyFromCString(&createSessionReq->EndpointUrl, chConfig->url);
    }
    assert(SOPC_STATUS_OK == status);
}

void msg_session_bs__write_create_session_req_msg_sessionTimeout(
    const constants__t_msg_i msg_session_bs__create_req_msg)
{
    OpcUa_CreateSessionRequest* createSessionReq = (OpcUa_CreateSessionRequest*) msg_session_bs__create_req_msg;
    createSessionReq->RequestedSessionTimeout = SOPC_REQUESTED_SESSION_TIMEOUT;
}

void msg_session_bs__write_create_session_req_msg_crypto(
    const constants__t_msg_i msg_session_bs__p_req_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx,
    const constants__t_Nonce_i msg_session_bs__p_nonce,
    t_bool* const msg_session_bs__bret)
{
    *msg_session_bs__bret = false;
    SOPC_SecureChannel_Config* pSCCfg = NULL;
    OpcUa_CreateSessionRequest* pReq = (OpcUa_CreateSessionRequest*) msg_session_bs__p_req_msg;
    const SOPC_Buffer* pSerialCertCli = NULL;
    SOPC_ReturnStatus status = SOPC_STATUS_NOK;

    /* Retrieve the certificate */
    pSCCfg = SOPC_ToolkitClient_GetSecureChannelConfig(msg_session_bs__p_channel_config_idx);

    if (NULL == pSCCfg)
    {
        return;
    }

    pSerialCertCli = pSCCfg->crt_cli;

    if (NULL == pSerialCertCli)
    {
        return;
    }

    /* Write the Certificate */
    SOPC_ByteString_Clear(&pReq->ClientCertificate);

    assert(pSerialCertCli->length <= INT32_MAX);
    status =
        SOPC_ByteString_CopyFromBytes(&pReq->ClientCertificate, pSerialCertCli->data, (int32_t) pSerialCertCli->length);
    if (SOPC_STATUS_OK != status)
        return;
    pReq->ClientCertificate.Length = (int32_t) pSerialCertCli->length;

    /* Write the nonce */
    SOPC_ByteString_Clear(&pReq->ClientNonce);

    status = SOPC_ByteString_Copy(&pReq->ClientNonce, msg_session_bs__p_nonce);
    if (SOPC_STATUS_OK != status)
        return;

    SOPC_Certificate* pCertCli = NULL;

    if (SOPC_STATUS_OK != SOPC_KeyManager_SerializedCertificate_Deserialize(pSerialCertCli, &pCertCli))
        return;

    size_t len = 0;
    if (SOPC_STATUS_OK == SOPC_KeyManager_Certificate_GetMaybeApplicationUri(
                              pCertCli, (char**) &pReq->ClientDescription.ApplicationUri.Data, &len))
    {
        if (len <= INT32_MAX)
        {
            pReq->ClientDescription.ApplicationUri.Length = (int32_t) len;
        }
        *msg_session_bs__bret = true;
    }
    else
    {
        SOPC_Logger_TraceError(
            "write_create_session_req_msg_crypto: Failed to extract ApplicationUri from client certificate on "
            "scConfigIdx=%" PRIu32,
            msg_session_bs__p_channel_config_idx);
    }

    SOPC_KeyManager_Certificate_Free(pCertCli);
}

void msg_session_bs__write_create_session_msg_session_token(
    const constants__t_msg_i msg_session_bs__msg,
    const constants__t_session_token_i msg_session_bs__session_token)
{
    OpcUa_CreateSessionResponse* createSessionResp = (OpcUa_CreateSessionResponse*) msg_session_bs__msg;
    SOPC_ReturnStatus status;
    const SOPC_NodeId* nodeId = msg_session_bs__session_token;
    status = SOPC_NodeId_Copy(&createSessionResp->AuthenticationToken, nodeId);
    assert(SOPC_STATUS_OK == status);
    status = SOPC_NodeId_Copy(&createSessionResp->SessionId, nodeId);
    createSessionResp->SessionId.Data.Numeric += 10000;
    assert(SOPC_STATUS_OK == status);
}

void msg_session_bs__write_create_session_msg_session_revised_timeout(const constants__t_msg_i msg_session_bs__req_msg,
                                                                      const constants__t_msg_i msg_session_bs__resp_msg)
{
    OpcUa_CreateSessionRequest* createSessionReq = (OpcUa_CreateSessionRequest*) msg_session_bs__req_msg;
    OpcUa_CreateSessionResponse* createSessionResp = (OpcUa_CreateSessionResponse*) msg_session_bs__resp_msg;

    if (createSessionReq->RequestedSessionTimeout < SOPC_MIN_SESSION_TIMEOUT)
    {
        createSessionResp->RevisedSessionTimeout = SOPC_MIN_SESSION_TIMEOUT;
    }
    else if (createSessionReq->RequestedSessionTimeout > SOPC_MAX_SESSION_TIMEOUT)
    {
        createSessionResp->RevisedSessionTimeout = SOPC_MAX_SESSION_TIMEOUT;
    }
    else
    {
        createSessionResp->RevisedSessionTimeout = createSessionReq->RequestedSessionTimeout;
    }
}

void msg_session_bs__write_create_session_msg_server_endpoints(
    const constants__t_msg_i msg_session_bs__req_msg,
    const constants__t_msg_i msg_session_bs__resp_msg,
    const constants__t_endpoint_config_idx_i msg_session_bs__endpoint_config_idx,
    constants__t_StatusCode_i* const msg_session_bs__ret)
{
    OpcUa_CreateSessionRequest* createSessionReq = (OpcUa_CreateSessionRequest*) msg_session_bs__req_msg;
    OpcUa_CreateSessionResponse* createSessionResp = (OpcUa_CreateSessionResponse*) msg_session_bs__resp_msg;

    *msg_session_bs__ret = SOPC_Discovery_GetEndPointsDescriptions(
        msg_session_bs__endpoint_config_idx, true, &createSessionReq->EndpointUrl,
        (uint32_t*) &createSessionResp->NoOfServerEndpoints, &createSessionResp->ServerEndpoints);
}

void msg_session_bs__write_create_session_resp_msg_crypto(
    const constants__t_msg_i msg_session_bs__p_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx,
    const constants__t_Nonce_i msg_session_bs__p_nonce,
    const constants__t_SignatureData_i msg_session_bs__p_signature,
    t_bool* const msg_session_bs__bret)
{
    SOPC_SecureChannel_Config* pSCCfg = NULL;
    const SOPC_Buffer* pCrtSrv = NULL;
    SOPC_ReturnStatus status = SOPC_STATUS_OK;
    bool result = true;
    OpcUa_CreateSessionResponse* pResp = (OpcUa_CreateSessionResponse*) msg_session_bs__p_msg;
    OpcUa_SignatureData* pSig = msg_session_bs__p_signature;

    /* Retrieve the certificate */
    pSCCfg = SOPC_ToolkitServer_GetSecureChannelConfig(msg_session_bs__p_channel_config_idx);
    if (NULL == pSCCfg)
    {
        result = false;
    }
    if (result != false)
    {
        pCrtSrv = pSCCfg->crt_srv;
        if (NULL == pCrtSrv)
        {
            result = false;
        }
    }

    /* Write the Certificate */
    if (result != false)
    {
        SOPC_ByteString_Clear(&pResp->ServerCertificate);
        assert(pCrtSrv->length <= INT32_MAX);
        status = SOPC_ByteString_CopyFromBytes(&pResp->ServerCertificate, pCrtSrv->data, (int32_t) pCrtSrv->length);

        if (SOPC_STATUS_OK == status)
        {
            pResp->ServerCertificate.Length = (int32_t) pCrtSrv->length;
            /* TODO: should borrow a reference instead of copy */
            /* Copy Nonce */
            status = SOPC_ByteString_Copy(&pResp->ServerNonce, msg_session_bs__p_nonce);
        }

        /* TODO: should borrow a reference instead of copy */
        /* Copy Signature, which is not a built-in, so copy its fields */
        if (SOPC_STATUS_OK == status)
        {
            status = SOPC_String_Copy(&pResp->ServerSignature.Algorithm, &pSig->Algorithm);
        }
        if (SOPC_STATUS_OK == status)
        {
            status = SOPC_ByteString_Copy(&pResp->ServerSignature.Signature, &pSig->Signature);
        }

        if (status != SOPC_STATUS_OK)
        {
            result = false;
        }
    }

    *msg_session_bs__bret = result;
}

void msg_session_bs__write_activate_req_msg_locales(
    const constants__t_msg_i msg_session_bs__p_req_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx)
{
    SOPC_ReturnStatus status = SOPC_STATUS_OK;
    OpcUa_ActivateSessionRequest* pReq = (OpcUa_ActivateSessionRequest*) msg_session_bs__p_req_msg;
    SOPC_SecureChannel_Config* pSCCfg = NULL;
    int32_t i = 0;

    /* Retrieve the certificate */
    pSCCfg = SOPC_ToolkitClient_GetSecureChannelConfig(msg_session_bs__p_channel_config_idx);

    if (NULL == pSCCfg || pSCCfg->clientLocaleIds == NULL || pSCCfg->clientNoOfLocaleIds <= 0)
    {
        return;
    }

    pReq->LocaleIds = calloc((size_t) pSCCfg->clientNoOfLocaleIds, sizeof(SOPC_String));

    if (pReq->LocaleIds != NULL)
    {
        for (i = 0; status == SOPC_STATUS_OK && i < pReq->NoOfLocaleIds; i++)
        {
            status = SOPC_String_Copy(&pReq->LocaleIds[i], &pSCCfg->clientLocaleIds[i]);
        }

        if (SOPC_STATUS_OK == status)
        {
            pReq->NoOfLocaleIds = pSCCfg->clientNoOfLocaleIds;
        }
        else
        {
            SOPC_Logger_TraceWarning("msg_session_bs__write_activate_req_msg_locales: allocation of %" PRIi32
                                     " locale id / %" PRIi32 " locale ids failed.",
                                     i, pSCCfg->clientNoOfLocaleIds);

            for (i = 0; status == SOPC_STATUS_OK && i < pReq->NoOfLocaleIds; i++)
            {
                SOPC_String_Clear(&pReq->LocaleIds[i]);
            }
            free(pReq->LocaleIds);
            pReq->LocaleIds = NULL;
        }
    }
    else
    {
        SOPC_Logger_TraceWarning("msg_session_bs__write_activate_req_msg_locales: allocation of %" PRIi32
                                 " locale ids failed.",
                                 pSCCfg->clientNoOfLocaleIds);
    }
}

void msg_session_bs__write_activate_session_req_msg_crypto(const constants__t_msg_i msg_session_bs__activate_req_msg,
                                                           const constants__t_SignatureData_i msg_session_bs__signature,
                                                           t_bool* const msg_session_bs__bret)

{
    SOPC_ReturnStatus status = SOPC_STATUS_NOK;
    OpcUa_ActivateSessionRequest* pReq = (OpcUa_ActivateSessionRequest*) msg_session_bs__activate_req_msg;
    OpcUa_SignatureData* pSig = msg_session_bs__signature;

    /* Copy Signature, which is not a built-in, so copy its fields */
    /* TODO: should borrow a reference instead of copy */
    status = SOPC_String_Copy(&pReq->ClientSignature.Algorithm, &pSig->Algorithm);

    if (SOPC_STATUS_OK == status)
    {
        status = SOPC_ByteString_Copy(&pReq->ClientSignature.Signature, &pSig->Signature);
    }

    if (SOPC_STATUS_OK == status)
    {
        *msg_session_bs__bret = true;
    }
    else
    {
        *msg_session_bs__bret = false;
    }
}

void msg_session_bs__write_activate_session_resp_msg_crypto(const constants__t_msg_i msg_session_bs__activate_resp_msg,
                                                            const constants__t_Nonce_i msg_session_bs__nonce)
{
    OpcUa_ActivateSessionResponse* pResp = (OpcUa_ActivateSessionResponse*) msg_session_bs__activate_resp_msg;
    SOPC_ReturnStatus status = SOPC_STATUS_NOK;

    /* Write the nonce */
    /* TODO: this can also fail because of the malloc */
    status = SOPC_ByteString_Copy(&pResp->ServerNonce, msg_session_bs__nonce);
    assert(SOPC_STATUS_OK == status);
}

void msg_session_bs__write_create_session_req_msg_clientDescription(
    const constants__t_msg_i msg_session_bs__p_req_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx)
{
    SOPC_SecureChannel_Config* pSCCfg = NULL;
    OpcUa_CreateSessionRequest* pReq = (OpcUa_CreateSessionRequest*) msg_session_bs__p_req_msg;
    SOPC_ReturnStatus status = SOPC_STATUS_NOK;

    pReq->ClientDescription.ApplicationType = OpcUa_ApplicationType_Client;

    /* Retrieve the certificate */
    pSCCfg = SOPC_ToolkitClient_GetSecureChannelConfig(msg_session_bs__p_channel_config_idx);

    if (NULL == pSCCfg)
    {
        return;
    }

    status = SOPC_String_CopyFromCString(&pReq->ClientDescription.ApplicationUri, pSCCfg->clientApplicationUri);
    if (SOPC_STATUS_OK != status)
    {
        // Trace a warning since the applicationUri is usually checked by server
        SOPC_Logger_TraceWarning(
            "No client application URI set in the create session request on channel config=%" PRIu32,
            msg_session_bs__p_channel_config_idx);
    }

    status = SOPC_String_CopyFromCString(&pReq->ClientDescription.ProductUri, pSCCfg->clientProductUri);
    if (SOPC_STATUS_OK != status)
    {
        SOPC_Logger_TraceInfo("No client product URI set in the create session request on channel config=%" PRIu32,
                              msg_session_bs__p_channel_config_idx);
    }

    status = SOPC_LocalizedText_Copy(&pReq->ClientDescription.ApplicationName, pSCCfg->clientApplicationName);
    if (SOPC_STATUS_OK != status)
    {
        SOPC_Logger_TraceInfo("No client application name set in the create session request on channel config=%" PRIu32,
                              msg_session_bs__p_channel_config_idx);
    }
}

void msg_session_bs__write_create_session_req_msg_maxResponseMessageSize(
    const constants__t_msg_i msg_session_bs__p_req_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx)
{
    // We may set the size coherent with the maximum size on SC (but information not available in services)
    (void) msg_session_bs__p_req_msg;
    (void) msg_session_bs__p_channel_config_idx;
}

void msg_session_bs__write_create_session_req_msg_sessionName(
    const constants__t_msg_i msg_session_bs__p_req_msg,
    const constants__t_session_i msg_session_bs__p_session,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx)
{
    (void) msg_session_bs__p_req_msg;
    (void) msg_session_bs__p_session;
    (void) msg_session_bs__p_channel_config_idx;
}

void msg_session_bs__write_create_session_resp_msg_maxRequestMessageSize(
    const constants__t_msg_i msg_session_bs__p_resp_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx)
{
    // We may set the size coherent with the maximum size on SC (but information not available in services)
    (void) msg_session_bs__p_resp_msg;
    (void) msg_session_bs__p_channel_config_idx;
}

void msg_session_bs__create_session_resp_check_server_certificate(
    const constants__t_msg_i msg_session_bs__p_resp_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx,
    t_bool* const msg_session_bs__valid)
{
    *msg_session_bs__valid = false;
    SOPC_SecureChannel_Config* pSCCfg = NULL;
    bool ignoreCertificate = false;
    bool sameCertificate = false;
    constants__t_SecurityPolicy SCsecPol = constants__e_secpol_B256S256;
    constants__t_SecurityPolicy userSecPol = constants__e_secpol_B256S256;

    OpcUa_CreateSessionResponse* pResp = (OpcUa_CreateSessionResponse*) msg_session_bs__p_resp_msg;

    /* Retrieve the certificate */
    pSCCfg = SOPC_ToolkitClient_GetSecureChannelConfig(msg_session_bs__p_channel_config_idx);

    if (NULL == pSCCfg)
    {
        return;
    }

    /* First check if the certificate is the same, if it is not check if it is really necessary */

    if (pSCCfg->crt_srv != NULL && pResp->ServerCertificate.Length > 0)
    {
        const SOPC_Buffer* scSrvCert = SOPC_KeyManager_SerializedCertificate_Data(pSCCfg->crt_srv);

        if (scSrvCert->length == (uint32_t) pResp->ServerCertificate.Length)
        {
            int comparison = memcmp(scSrvCert->data, pResp->ServerCertificate.Data, scSrvCert->length);
            sameCertificate = (comparison == 0);
        }
    }

    if (sameCertificate)
    {
        *msg_session_bs__valid = true;
        return;
    }

    /* Certificate is different, check if it can be ignored (only when SC security policy != NONE) */

    bool validSecPolicy = util_channel__SecurityPolicy_C_to_B(pSCCfg->reqSecuPolicyUri, &SCsecPol);

    if (!validSecPolicy)
    {
        SOPC_Logger_TraceError(
            "msg_session_bs__create_session_resp_check_server_certificate: invalid security policy %s in channel "
            "config %" PRIu32,
            pSCCfg->reqSecuPolicyUri, msg_session_bs__p_channel_config_idx);
        return;
    }

    if (constants__e_secpol_None == SCsecPol) // Current SC security policy is None
    {
        /* From OPC UA part 4, CreateSession Service Parameters:
           If the securityPolicyUri is NONE and none of the UserTokenPolicies requires
           encryption, the Client shall ignore the ApplicationInstanceCertificate. */
        ignoreCertificate = true;
        for (int32_t i = 0; i < pResp->NoOfServerEndpoints && ignoreCertificate; i++)
        {
            /* For each EndpointDescription */
            OpcUa_EndpointDescription* pEPdesc = &pResp->ServerEndpoints[i];
            validSecPolicy =
                util_channel__SecurityPolicy_C_to_B(SOPC_String_GetRawCString(&pEPdesc->SecurityPolicyUri), &SCsecPol);
            if (!validSecPolicy)
            {
                SOPC_Logger_TraceError(
                    "msg_session_bs__create_session_resp_check_server_certificate: invalid security policy %s in "
                    "create session response on channel config %" PRIu32,
                    SOPC_String_GetRawCString(&pEPdesc->SecurityPolicyUri), msg_session_bs__p_channel_config_idx);
                return;
            }

            if (constants__e_secpol_None == SCsecPol) // Endpoint description security policy is None
            {
                for (int32_t j = 0; j < pEPdesc->NoOfUserIdentityTokens; j++)
                {
                    /* For each user token policy */
                    OpcUa_UserTokenPolicy* pUserToken = &pEPdesc->UserIdentityTokens[j];

                    if (pUserToken->SecurityPolicyUri.Length > 0)
                    {
                        validSecPolicy = util_channel__SecurityPolicy_C_to_B(
                            SOPC_String_GetRawCString(&pUserToken->SecurityPolicyUri), &userSecPol);
                        if (!validSecPolicy)
                        {
                            SOPC_Logger_TraceError(
                                "msg_session_bs__create_session_resp_check_server_certificate: invalid security policy "
                                "%s "
                                "in "
                                "create session response on channel config %" PRIu32,
                                SOPC_String_GetRawCString(&pUserToken->SecurityPolicyUri),
                                msg_session_bs__p_channel_config_idx);
                            return;
                        }

                        if (constants__e_secpol_None != userSecPol) // User security policy != None
                        {
                            /* The certificate can be necessary in case we change of user */
                            ignoreCertificate = false;
                        }
                    } // else no user security policy => no need of certificate
                }
            }
        }
    }

    if (ignoreCertificate)
    {
        *msg_session_bs__valid = true;
        return;
    }

    SOPC_Logger_TraceWarning(
        "msg_session_bs__create_session_resp_check_server_certificate: server certificate verification failed");
}

void msg_session_bs__create_session_resp_check_server_endpoints(
    const constants__t_msg_i msg_session_bs__p_resp_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx,
    t_bool* const msg_session_bs__valid)
{
    *msg_session_bs__valid = false;
    SOPC_SecureChannel_Config* pSCCfg = NULL;

    OpcUa_CreateSessionResponse* pResp = (OpcUa_CreateSessionResponse*) msg_session_bs__p_resp_msg;

    pSCCfg = SOPC_ToolkitClient_GetSecureChannelConfig(msg_session_bs__p_channel_config_idx);

    if (NULL == pSCCfg)
    {
        return;
    }

    if (pSCCfg->serverEndpoints == NULL || pSCCfg->nbServerEndpoints <= 0)
    {
        SOPC_Logger_TraceInfo(
            "msg_session_bs__create_session_resp_check_server_endpoints: no endpoint description in channel config "
            "%" PRIu32 " with the security policy %s",
            msg_session_bs__p_channel_config_idx, pSCCfg->reqSecuPolicyUri);

        // We have to consider in this case that connection configuration is not created from discovery endpoint
        *msg_session_bs__valid = true;
        return;
    }

    /* Check endpoint descriptions are the same */
    bool sameEndpoints = true;

    if (pSCCfg->nbServerEndpoints != pResp->NoOfServerEndpoints)
    {
        sameEndpoints = false;
    }

    for (int32_t i = 0; i < pSCCfg->nbServerEndpoints && sameEndpoints; i++)
    {
        OpcUa_EndpointDescription* left = &pSCCfg->serverEndpoints[i];
        OpcUa_EndpointDescription* right = &pResp->ServerEndpoints[i];

        // EndpointURL
        sameEndpoints = SOPC_String_Equal(&left->EndpointUrl, &right->EndpointUrl);

        // SecurityMode
        sameEndpoints = sameEndpoints && (left->SecurityMode != right->SecurityMode);

        // SecurityPolicyUri
        sameEndpoints = sameEndpoints && SOPC_String_Equal(&left->SecurityPolicyUri, &right->SecurityPolicyUri);

        // UserIdentityTokens
        sameEndpoints = sameEndpoints && SOPC_String_Equal(&left->SecurityPolicyUri, &right->SecurityPolicyUri);

        // TransportProfileUri
        sameEndpoints = sameEndpoints && SOPC_String_Equal(&left->TransportProfileUri, &right->TransportProfileUri);

        // SecurityLevel
        sameEndpoints = sameEndpoints && (left->SecurityLevel != right->SecurityLevel);
    }

    *msg_session_bs__valid = sameEndpoints;

    if (sameEndpoints == false)
    {
        SOPC_Logger_TraceWarning(
            "msg_session_bs__create_session_resp_check_server_endpoints: server certificate verification failed");
    }
}

void msg_session_bs__create_session_resp_export_maxRequestMessageSize(
    const constants__t_msg_i msg_session_bs__p_resp_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx)
{
    OpcUa_CreateSessionResponse* pResp = (OpcUa_CreateSessionResponse*) msg_session_bs__p_resp_msg;

    if (pResp->MaxRequestMessageSize > 0)
    {
        (void) msg_session_bs__p_channel_config_idx;

        // TODO: report the maxRequestMessageSize to the SC which then can adapt the size limit if more restrictive than
        // the one at TCP layer

        SOPC_Logger_TraceWarning("Create session response maxRequestMessageSize value ignored");
    }
}

void msg_session_bs__create_session_req_export_maxResponseMessageSize(
    const constants__t_msg_i msg_session_bs__p_req_msg,
    const constants__t_channel_config_idx_i msg_session_bs__p_channel_config_idx)
{
    OpcUa_CreateSessionRequest* pResp = (OpcUa_CreateSessionRequest*) msg_session_bs__p_req_msg;

    if (pResp->MaxResponseMessageSize > 0)
    {
        (void) msg_session_bs__p_channel_config_idx;

        // TODO: report the maxRequestMessageSize to the SC which then can adapt the size limit if more restrictive than
        // the one at TCP layer

        SOPC_Logger_TraceWarning("Create session response maxRequestMessageSize value ignored");
    }
}
