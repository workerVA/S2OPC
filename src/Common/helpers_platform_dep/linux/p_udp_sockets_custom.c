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

#include <arpa/inet.h>
#include <assert.h>
#include <errno.h>
#include <ifaddrs.h>
#include <linux/errqueue.h>
#include <linux/types.h>
#include <net/if.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <time.h>

#include "p_udp_sockets_custom.h"

#ifndef SO_EE_ORIGIN_TXTIME
#define SO_EE_ORIGIN_TXTIME 6
#define SO_EE_CODE_TXTIME_INVALID_PARAM 1
#define SO_EE_CODE_TXTIME_MISSED 2
#endif

SOPC_ReturnStatus SOPC_UDP_SO_TXTIME_Socket_Option(const char* interface, Socket* sock)
{
    SPOC_Socket_txtime txtimeSock;
    static uint16_t useDeadlineMode = 0;
    static uint16_t receiveErrors = 0;
    uint32_t soPriority = 3;
    const int trueInt = true;
    int setOptStatus = -1;
    int res = 0;
    struct ifreq nwInterface;

    setOptStatus = setsockopt(*sock, SOL_SOCKET, SO_PRIORITY, &soPriority, sizeof(soPriority));
    if (setOptStatus < 0)
    {
        return SOPC_STATUS_NOK;
    }

    setOptStatus = setsockopt(*sock, SOL_SOCKET, SO_REUSEADDR, (const void*) &trueInt, sizeof(int));
    if (setOptStatus < 0)
    {
        return SOPC_STATUS_NOK;
    }

    memset(&nwInterface, 0, sizeof(nwInterface));
    strncpy(nwInterface.ifr_name, interface, sizeof(nwInterface.ifr_name) - 1);
    res = ioctl(*sock, SIOCGIFINDEX, &nwInterface);
    if (res < 0)
    {
        return SOPC_STATUS_NOK;
    }

    setOptStatus = setsockopt(*sock, SOL_SOCKET, SO_BINDTODEVICE, (void*) &nwInterface, sizeof(nwInterface));
    if (setOptStatus < 0)
    {
        printf("Interface selection failed\n");
        return SOPC_STATUS_NOK;
    }

    memset(&txtimeSock, 0, sizeof(txtimeSock));
    txtimeSock.clockid = CLOCK_TAI;
    txtimeSock.flags = (useDeadlineMode | receiveErrors);
    setOptStatus = setsockopt(*sock, SOL_SOCKET, SO_TXTIME, &txtimeSock, sizeof(txtimeSock));
    if (setOptStatus < 0)
    {
        SOPC_UDP_Socket_Close(sock);
        return SOPC_STATUS_NOK;
    }

    return SOPC_STATUS_OK;
}

SOPC_ReturnStatus SOPC_TX_UDP_send(int sockAddress,
                                   void* txBuffer,
                                   uint32_t txBuffLen,
                                   uint64_t txtime,
                                   const char* node,
                                   const char* service)
{
    char control[CMSG_SPACE(sizeof(txtime))] = {0};
    ssize_t res;
    struct cmsghdr* controlMessage;
    struct msghdr message;
    struct iovec fdIOBuffer;
    static struct in_addr mcastAddr;
    struct sockaddr_in sockIpAddr;

    if (!inet_aton(node, &mcastAddr))
    {
        return SOPC_STATUS_NOK;
    }

    memset(&sockIpAddr, 0, sizeof(sockIpAddr));
    sockIpAddr.sin_family = AF_INET;
    sockIpAddr.sin_addr = mcastAddr;
    sockIpAddr.sin_port = htons(strtol(service, NULL, 10));

    fdIOBuffer.iov_base = txBuffer;
    fdIOBuffer.iov_len = (size_t) txBuffLen;

    memset(&message, 0, sizeof(message));
    message.msg_name = &sockIpAddr;
    message.msg_namelen = sizeof(sockIpAddr);
    message.msg_iov = &fdIOBuffer;
    message.msg_iovlen = 1;
    message.msg_control = control;
    message.msg_controllen = sizeof(control);

    controlMessage = CMSG_FIRSTHDR(&message);
    controlMessage->cmsg_level = SOL_SOCKET;
    controlMessage->cmsg_type = SCM_TXTIME;
    controlMessage->cmsg_len = CMSG_LEN(sizeof(__u64));
    memcpy(CMSG_DATA(controlMessage), &txtime, sizeof(__u64));
    res = sendmsg(sockAddress, &message, 0);
    if ((uint32_t) res != txBuffLen || res < 1)
    {
        return SOPC_STATUS_NOK;
    }

    return SOPC_STATUS_OK;
}

SOPC_ReturnStatus SOPC_TX_UDP_Socket_Error_Queue(int sockFd)
{
    uint8_t messageControl[CMSG_SPACE(sizeof(struct sock_extended_err))];
    unsigned char errBuffer[sizeof(250)];
    struct sock_extended_err* sockErr;
    struct cmsghdr* controlMessage;
    __u64 timestamp = 0;

    struct iovec fdIOBuffer = {.iov_base = errBuffer, .iov_len = sizeof(errBuffer)};
    struct msghdr message = {.msg_iov = &fdIOBuffer,
                             .msg_iovlen = 1,
                             .msg_control = messageControl,
                             .msg_controllen = sizeof(messageControl)};

    if (recvmsg(sockFd, &message, MSG_ERRQUEUE) == -1)
    {
        printf("Receive message failed from error queue\n");
        return SOPC_STATUS_NOK;
    }
    controlMessage = CMSG_FIRSTHDR(&message);
    while (controlMessage != NULL)
    {
        sockErr = (void*) CMSG_DATA(controlMessage);
        if (sockErr->ee_origin == SO_EE_ORIGIN_TXTIME)
        {
            timestamp = ((__u64) sockErr->ee_data << 32) + sockErr->ee_info;
            switch (sockErr->ee_code)
            {
            case SO_EE_CODE_TXTIME_INVALID_PARAM:
                fprintf(stderr, "Packet with timestamp %llu dropped\n", timestamp);
                return SOPC_STATUS_NOK;
            case SO_EE_CODE_TXTIME_MISSED:
                fprintf(stderr, "Packet with timestamp %llu dropped\n", timestamp);
                return SOPC_STATUS_NOK;
            default:
                return SOPC_STATUS_OK;
            }
        }

        controlMessage = CMSG_NXTHDR(&message, controlMessage);
    }

    return SOPC_STATUS_OK;
}
