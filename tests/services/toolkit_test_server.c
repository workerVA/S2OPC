/*
 *  Copyright (C) 2017 Systerel and others.
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as
 *  published by the Free Software Foundation, either version 3 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <stdio.h>
#include <stdlib.h>

#include "sopc_crypto_profiles.h"
#include "sopc_crypto_provider.h"
#include "sopc_pki_stack.h"
#include "io_dispatch_mgr.h"

#include "sopc_time.h"
#include "opcua_identifiers.h"
#include "opcua_statuscodes.h"
#include "sopc_encodeable.h"

#include "sopc_toolkit_config.h"
#include "sopc_toolkit_async_api.h"

#include "wrap_read.h"

#include "sopc_addspace.h"


#define ENDPOINT_URL "opc.tcp://localhost:4841"

static int endpointClosed = false;
static bool secuActive = !false;

void Test_ComEvent_Fct(SOPC_App_Com_Event event,
                         void*              param,
                         SOPC_StatusCode    status){
    (void) param;
    (void) status;
  if(event == SE_CLOSED_ENDPOINT){
    printf("<Test_Server_Toolkit: closed endpoint event: OK\n");
    endpointClosed = !false;
  }else{
    printf("<Test_Server_Toolkit: unexpected endpoint event %d : NOK\n", event);
  }
}

int main(void)
{
  SOPC_StatusCode status = STATUS_OK;
  constants__t_endpoint_config_idx_i epConfigIdx = constants__c_endpoint_config_idx_indet;
  SOPC_Endpoint_Config epConfig;
  // Sleep timeout in milliseconds
  const uint32_t sleepTimeout = 500;
  // Loop timeout in milliseconds
  uint32_t loopTimeout = 20000;
  // Counter to stop waiting on timeout
  uint32_t loopCpt = 0;

  // Secu policy configuration: 
  static SOPC_Certificate * serverCertificate = NULL;
  static SOPC_AsymmetricKey *  asymmetricKey = NULL;
  static SOPC_Certificate * authCertificate = NULL;
  static SOPC_PKIProvider * pkiProvider = NULL;

  SOPC_SecurityPolicy secuConfig[3];
  SOPC_String_Initialize(&secuConfig[0].securityPolicy);
  SOPC_String_Initialize(&secuConfig[1].securityPolicy);
  SOPC_String_Initialize(&secuConfig[2].securityPolicy);

  if(STATUS_OK == status){

      status = SOPC_String_AttachFromCstring(&secuConfig[0].securityPolicy,
                                           SOPC_SecurityPolicy_None_URI);
      secuConfig[0].securityModes = SOPC_SECURITY_MODE_NONE_MASK;
      if(STATUS_OK == status){
          status = SOPC_String_AttachFromCstring(&secuConfig[1].securityPolicy,
                                               SOPC_SecurityPolicy_Basic256_URI);
          secuConfig[1].securityModes = SOPC_SECURITY_MODE_SIGN_MASK;
      }
      if(STATUS_OK == status){
        status = SOPC_String_AttachFromCstring(&secuConfig[2].securityPolicy,
                                             SOPC_SecurityPolicy_Basic256Sha256_URI);
        secuConfig[2].securityModes = SOPC_SECURITY_MODE_SIGNANDENCRYPT_MASK;
      }
  }

  // Init unique endpoint structure
  epConfig.endpointURL = ENDPOINT_URL;
  if (secuActive != false){

      status = SOPC_KeyManager_Certificate_CreateFromFile("./server_public/server.der", &serverCertificate);
      epConfig.serverCertificate = serverCertificate;

      if(STATUS_OK == status){    
          status = SOPC_KeyManager_AsymmetricKey_CreateFromFile("./server_private/server.key", &asymmetricKey, NULL, 0);
          epConfig.serverKey = asymmetricKey;
      }
      if(STATUS_OK == status){
          status = SOPC_KeyManager_Certificate_CreateFromFile("./trusted/cacert.der", &authCertificate);
      }

      if(STATUS_OK == status){
          status = SOPC_PKIProviderStack_Create(authCertificate, NULL, &pkiProvider);
          epConfig.pki = pkiProvider;
      }
    if(STATUS_OK != status){
      printf("<Test_Server_Toolkit: Failed loading certificates and key (check paths are valid)\n");
    }else{
      printf("<Test_Server_Toolkit: Certificates and key loaded\n");
    }
  } else {
      epConfig.serverCertificate = NULL;
      epConfig.serverKey = NULL;
      epConfig.pki = NULL;
  }
  
  epConfig.secuConfigurations = secuConfig;
  if(secuActive){
    epConfig.nbSecuConfigs = 3; 
  }else{
    epConfig.nbSecuConfigs = 1; 
  }

  // Init stack configuration
  if(STATUS_OK == status){
    status = SOPC_Toolkit_Initialize(Test_ComEvent_Fct);
    if(STATUS_OK != status){
      printf("<Test_Server_Toolkit: Failed initializing\n");
    }else{
      printf("<Test_Server_Toolkit: initialized\n");
    }
  }

  // Define server address space 
  if(STATUS_OK == status){
    status = SOPC_ToolkitServer_SetAddressSpaceConfig(&addressSpace);    
    if(STATUS_OK != status){
      printf("<Test_Server_Toolkit: Failed to configure the @ space\n");
    }else{
      printf("<Test_Server_Toolkit: @ space configured\n");
    }
  }

  // Add endpoint description configuration
  if(STATUS_OK == status){
    epConfigIdx = SOPC_ToolkitServer_AddEndpointConfig(&epConfig);    
    if(epConfigIdx != constants__c_endpoint_config_idx_indet){
      status = SOPC_Toolkit_Configured();
    }else{
      status = STATUS_NOK;
    }
    if(STATUS_OK != status){
      printf("<Test_Server_Toolkit: Failed to configure the endpoint\n");
    }else{
      printf("<Test_Server_Toolkit: Endpoint configured\n");
    }
  }

  // Asynchronous request to open the endpoint
  if(STATUS_OK == status){
      printf("<Test_Server_Toolkit: Opening endpoint... \n");
      SOPC_ToolkitServer_AsyncOpenEndpoint(epConfigIdx);
  }

  // Run the server until timeout or notification that endpoint is closed
  loopCpt = 0;
  loopTimeout = 50000;
  while (STATUS_OK == status && endpointClosed == false && loopCpt * sleepTimeout <= loopTimeout)
    {
        loopCpt++;
        // Retrieve received messages on socket
        SOPC_Sleep(sleepTimeout);
    }

  // Asynchronous request to close the endpoint
  SOPC_ToolkitServer_AsyncCloseEndpoint(epConfigIdx);

  // Wait until endpoint is closed
  loopCpt = 0;
  loopTimeout = 1000;
  while (STATUS_OK == status && endpointClosed == false && loopCpt * sleepTimeout <= loopTimeout)
    {
        loopCpt++;
        // Retrieve received messages on socket
        SOPC_Sleep(sleepTimeout);
    }

  if(loopCpt * sleepTimeout > loopTimeout){
    status = OpcUa_BadTimeout;
  }

  // Clear the toolkit configuration and stop toolkit threads
  SOPC_Toolkit_Clear();

  if(STATUS_OK == status){
    printf("<Test_Server_Toolkit final result: OK\n");
  }else{
    printf("<Test_Server_Toolkit final result: NOK with status = '%X'\n", status);
  }

  // Deallocate locally allocated data

  SOPC_String_Clear(&secuConfig[0].securityPolicy);
  SOPC_String_Clear(&secuConfig[1].securityPolicy);
  SOPC_String_Clear(&secuConfig[2].securityPolicy);

  
  if (secuActive != false) {
      SOPC_KeyManager_Certificate_Free(serverCertificate);
      SOPC_KeyManager_AsymmetricKey_Free(asymmetricKey);
      SOPC_KeyManager_Certificate_Free(authCertificate);
      SOPC_PKIProviderStack_Free(pkiProvider);
  }

  return status;
}
