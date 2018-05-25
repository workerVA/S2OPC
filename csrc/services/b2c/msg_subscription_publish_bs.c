/*
 *  Copyright (C) 2018 Systerel and others.
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

#include "msg_subscription_publish_bs.h"

#include "util_b2c.h"

#include "sopc_services_api_internal.h"
#include "sopc_time.h"
#include "sopc_types.h"

/*--------------
   SEES Clause
  --------------*/
#include "constants.h"
#include "message_in_bs.h"
#include "message_out_bs.h"
#include "request_handle_bs.h"

static const uint64_t SOPC_MILLISECOND_TO_100_NANOSECONDS = 10000; // 10^4

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void msg_subscription_publish_bs__INITIALISATION(void) {}

/*--------------------
   OPERATIONS Clause
  --------------------*/
void msg_subscription_publish_bs__alloc_notification_message(
    const t_entier4 msg_subscription_publish_bs__p_nb_monitored_item_notifications,
    t_bool* const msg_subscription_publish_bs__bres,
    constants__t_notif_msg_i* const msg_subscription_publish_bs__p_notifMsg)
{
    *msg_subscription_publish_bs__bres = false;
    OpcUa_NotificationMessage* notifMsg = NULL;
    OpcUa_DataChangeNotification* dataChangeNotif = NULL;
    SOPC_ReturnStatus status = SOPC_STATUS_NOK;

    if ((uint64_t) msg_subscription_publish_bs__p_nb_monitored_item_notifications <
        SIZE_MAX / sizeof(OpcUa_MonitoredItemNotification))
    {
        SOPC_Encodeable_Create(&OpcUa_NotificationMessage_EncodeableType, (void**) &notifMsg);
        if (NULL != notifMsg)
        {
            notifMsg->PublishTime = SOPC_Time_GetCurrentTimeUTC();
            notifMsg->NoOfNotificationData =
                1; // Only 1 DataChangeNotification supported (not event & no status change)

            // Create the extension object
            notifMsg->NotificationData = malloc(sizeof(SOPC_ExtensionObject));

            if (NULL != notifMsg->NotificationData)
            {
                SOPC_ExtensionObject_Initialize(notifMsg->NotificationData);
                // Create the notification data extension object
                status = SOPC_Encodeable_CreateExtension(notifMsg->NotificationData,
                                                         &OpcUa_DataChangeNotification_EncodeableType,
                                                         (void**) &dataChangeNotif);

                if (SOPC_STATUS_OK != status)
                {
                    free(notifMsg->NotificationData);
                    SOPC_Encodeable_Delete(&OpcUa_NotificationMessage_EncodeableType, (void**) &notifMsg);
                }
            }

            if (SOPC_STATUS_OK == status)
            {
                dataChangeNotif->NoOfMonitoredItems = msg_subscription_publish_bs__p_nb_monitored_item_notifications;
                dataChangeNotif->MonitoredItems =
                    malloc((size_t) msg_subscription_publish_bs__p_nb_monitored_item_notifications *
                           sizeof(OpcUa_MonitoredItemNotification));

                if (NULL != dataChangeNotif->MonitoredItems)
                {
                    for (int32_t i = 0; i < msg_subscription_publish_bs__p_nb_monitored_item_notifications; i++)
                    {
                        OpcUa_MonitoredItemNotification_Initialize(&dataChangeNotif->MonitoredItems[i]);
                    }
                    *msg_subscription_publish_bs__p_notifMsg = notifMsg;
                    *msg_subscription_publish_bs__bres = true;
                }
                else
                {
                    SOPC_Encodeable_Delete(&OpcUa_NotificationMessage_EncodeableType, (void**) &notifMsg);
                }
            }
        }
    }
}

void msg_subscription_publish_bs__generate_internal_send_publish_response_event(
    const constants__t_session_i msg_subscription_publish_bs__p_session,
    const constants__t_msg_i msg_subscription_publish_bs__p_publish_resp_msg,
    const constants__t_server_request_handle_i msg_subscription_publish_bs__p_req_handle,
    const constants__t_request_context_i msg_subscription_publish_bs__p_req_context,
    const constants__t_StatusCode_i msg_subscription_publish_bs__p_statusCode)
{
    SOPC_Internal_AsyncSendMsgData* eventData = malloc(sizeof(SOPC_Internal_AsyncSendMsgData));
    if (NULL != eventData)
    {
        eventData->msgToSend = msg_subscription_publish_bs__p_publish_resp_msg;
        eventData->requestHandle = msg_subscription_publish_bs__p_req_handle;
        eventData->requestId = msg_subscription_publish_bs__p_req_context;

        SOPC_Services_InternalEnqueuePrioEvent(SE_TO_SE_SERVER_SEND_ASYNC_PUB_RESP_PRIO,
                                               (uint32_t) msg_subscription_publish_bs__p_session, eventData,
                                               (uintptr_t) msg_subscription_publish_bs__p_statusCode);
    }
    else
    {
        // TODO: log ?
    }
}

void msg_subscription_publish_bs__get_msg_header_expiration_time(
    const constants__t_msg_header_i msg_subscription_publish_bs__p_req_header,
    constants__t_timeref_i* const msg_subscription_publish_bs__req_expiration_time)
{
    OpcUa_RequestHeader* pubReqHeader = msg_subscription_publish_bs__p_req_header;
    *msg_subscription_publish_bs__req_expiration_time = SOPC_TimeReference_GetCurrent();

    int64_t dtDelta = SOPC_Time_GetCurrentTimeUTC() - pubReqHeader->Timestamp;
    uint64_t millisecondsToTarget = 0;
    if (dtDelta > 0)
    {
        if (pubReqHeader->TimeoutHint >= (uint64_t) dtDelta / SOPC_MILLISECOND_TO_100_NANOSECONDS)
        {
            millisecondsToTarget = pubReqHeader->TimeoutHint - (uint64_t) dtDelta / SOPC_MILLISECOND_TO_100_NANOSECONDS;
        }
        else
        {
            // Already expired
            millisecondsToTarget = 0;
            // TODO: log ?
        }
    }
    else
    {
        // Keep only timeoutHint from current time
        millisecondsToTarget = pubReqHeader->TimeoutHint;
    }
    *msg_subscription_publish_bs__req_expiration_time =
        SOPC_TimeReference_AddMilliseconds(*msg_subscription_publish_bs__req_expiration_time, millisecondsToTarget);
}

void msg_subscription_publish_bs__is_valid_notif_msg(
    const constants__t_notif_msg_i msg_subscription_publish_bs__p_notifMsg,
    t_bool* const msg_subscription_publish_bs__bres)
{
    *msg_subscription_publish_bs__bres = msg_subscription_publish_bs__p_notifMsg != NULL;
}

void msg_subscription_publish_bs__set_msg_publish_resp_notificationMsg(
    const constants__t_msg_i msg_subscription_publish_bs__p_resp_msg,
    const constants__t_notif_msg_i msg_subscription_publish_bs__p_notifMsg,
    const t_bool msg_subscription_publish_bs__p_moreNotifs)
{
    OpcUa_PublishResponse* pubResp = (OpcUa_PublishResponse*) msg_subscription_publish_bs__p_resp_msg;
    pubResp->NotificationMessage = *msg_subscription_publish_bs__p_notifMsg;
    free(msg_subscription_publish_bs__p_notifMsg);
    pubResp->MoreNotifications = msg_subscription_publish_bs__p_moreNotifs;
}

void msg_subscription_publish_bs__set_msg_publish_resp_subscription(
    const constants__t_msg_i msg_subscription_publish_bs__p_resp_msg,
    const constants__t_subscription_i msg_subscription_publish_bs__p_subscription)
{
    OpcUa_PublishResponse* pubResp = (OpcUa_PublishResponse*) msg_subscription_publish_bs__p_resp_msg;
    pubResp->SubscriptionId = (uint32_t) msg_subscription_publish_bs__p_subscription;
}

void msg_subscription_publish_bs__set_notification_message_sequence_number(
    const constants__t_notif_msg_i msg_subscription_publish_bs__p_notifMsg,
    const constants__t_sub_seq_num_i msg_subscription_publish_bs__p_seq_num)
{
    msg_subscription_publish_bs__p_notifMsg->SequenceNumber = msg_subscription_publish_bs__p_seq_num;
}

void msg_subscription_publish_bs__setall_notification_msg_monitored_item_notif(
    const constants__t_notif_msg_i msg_subscription_publish_bs__p_notifMsg,
    const t_entier4 msg_subscription_publish_bs__p_index,
    const constants__t_monitoredItemId_i msg_subscription_publish_bs__p_monitored_item_id,
    const constants__t_client_handle_i msg_subscription_publish_bs__p_clientHandle,
    const constants__t_WriteValuePointer_i msg_subscription_publish_bs__p_wv_pointer)
{
    (void) msg_subscription_publish_bs__p_monitored_item_id;
    OpcUa_DataChangeNotification* dataChangeNotif =
        (OpcUa_DataChangeNotification*) msg_subscription_publish_bs__p_notifMsg->NotificationData->Body.Object.Value;
    dataChangeNotif->MonitoredItems[msg_subscription_publish_bs__p_index - 1].ClientHandle =
        msg_subscription_publish_bs__p_clientHandle;
    SOPC_DataValue_Copy(&dataChangeNotif->MonitoredItems[msg_subscription_publish_bs__p_index - 1].Value,
                        &msg_subscription_publish_bs__p_wv_pointer->Value);

    OpcUa_WriteValue_Clear(msg_subscription_publish_bs__p_wv_pointer);
    free(msg_subscription_publish_bs__p_wv_pointer);
}
