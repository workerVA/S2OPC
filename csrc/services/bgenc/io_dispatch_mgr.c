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

/******************************************************************************

 File Name            : io_dispatch_mgr.c

 Date                 : 15/02/2018 15:01:12

 C Translator Version : tradc Java V1.0 (14/03/2012)

******************************************************************************/

/*------------------------
   Exported Declarations
  ------------------------*/
#include "io_dispatch_mgr.h"

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void io_dispatch_mgr__INITIALISATION(void) {}

/*--------------------
   OPERATIONS Clause
  --------------------*/
void io_dispatch_mgr__get_msg_header_type(const constants__t_msg_type_i io_dispatch_mgr__msg_typ,
                                          constants__t_msg_header_type_i* const io_dispatch_mgr__header_type)
{
    *io_dispatch_mgr__header_type = constants__c_msg_header_type_indet;
    switch (io_dispatch_mgr__msg_typ)
    {
    case constants__e_msg_session_create_req:
    case constants__e_msg_session_activate_req:
    case constants__e_msg_session_close_req:
    case constants__e_msg_session_cancel_req:
    case constants__e_msg_node_add_nodes_req:
    case constants__e_msg_node_add_references_req:
    case constants__e_msg_node_delete_nodes_req:
    case constants__e_msg_node_delete_references_req:
    case constants__e_msg_view_browse_req:
    case constants__e_msg_view_browse_next_req:
    case constants__e_msg_view_translate_browse_paths_to_node_ids_req:
    case constants__e_msg_view_register_nodes_req:
    case constants__e_msg_view_unregister_nodes_req:
    case constants__e_msg_query_first_req:
    case constants__e_msg_query_next_req:
    case constants__e_msg_attribute_read_req:
    case constants__e_msg_attribute_history_read_req:
    case constants__e_msg_attribute_write_req:
    case constants__e_msg_attribute_history_update_req:
    case constants__e_msg_method_call_req:
    case constants__e_msg_monitored_items_create_req:
    case constants__e_msg_monitored_items_modify_req:
    case constants__e_msg_monitored_items_set_monitoring_mode_req:
    case constants__e_msg_monitored_items_set_triggering_req:
    case constants__e_msg_monitored_items_delete_req:
    case constants__e_msg_subscription_create_req:
    case constants__e_msg_subscription_modify_req:
    case constants__e_msg_subscription_set_publishing_mode_req:
    case constants__e_msg_subscription_publish_req:
    case constants__e_msg_subscription_republish_req:
    case constants__e_msg_subscription_transfer_subscriptions_req:
    case constants__e_msg_subscription_delete_subscriptions_req:
    case constants__e_msg_discovery_find_servers_req:
    case constants__e_msg_discovery_find_servers_on_network_req:
    case constants__e_msg_discovery_get_endpoints_req:
    case constants__e_msg_discovery_register_server_req:
    case constants__e_msg_discovery_register_server2_req:
        *io_dispatch_mgr__header_type = constants__e_msg_request_type;
        break;
    case constants__e_msg_session_create_resp:
    case constants__e_msg_session_activate_resp:
    case constants__e_msg_session_close_resp:
    case constants__e_msg_session_cancel_resp:
    case constants__e_msg_node_add_nodes_resp:
    case constants__e_msg_node_add_references_resp:
    case constants__e_msg_node_delete_nodes_resp:
    case constants__e_msg_node_delete_references_resp:
    case constants__e_msg_view_browse_resp:
    case constants__e_msg_view_browse_next_resp:
    case constants__e_msg_view_translate_browse_paths_to_node_ids_resp:
    case constants__e_msg_view_register_nodes_resp:
    case constants__e_msg_view_unregister_nodes_resp:
    case constants__e_msg_query_first_resp:
    case constants__e_msg_query_next_resp:
    case constants__e_msg_attribute_read_resp:
    case constants__e_msg_attribute_history_read_resp:
    case constants__e_msg_attribute_write_resp:
    case constants__e_msg_attribute_history_update_resp:
    case constants__e_msg_method_call_resp:
    case constants__e_msg_monitored_items_create_resp:
    case constants__e_msg_monitored_items_modify_resp:
    case constants__e_msg_monitored_items_set_monitoring_mode_resp:
    case constants__e_msg_monitored_items_set_triggering_resp:
    case constants__e_msg_monitored_items_delete_resp:
    case constants__e_msg_subscription_create_resp:
    case constants__e_msg_subscription_modify_resp:
    case constants__e_msg_subscription_set_publishing_mode_resp:
    case constants__e_msg_subscription_publish_resp:
    case constants__e_msg_subscription_republish_resp:
    case constants__e_msg_subscription_transfer_subscriptions_resp:
    case constants__e_msg_subscription_delete_subscriptions_resp:
    case constants__e_msg_discovery_find_servers_resp:
    case constants__e_msg_discovery_find_servers_on_network_resp:
    case constants__e_msg_discovery_get_endpoints_resp:
    case constants__e_msg_discovery_register_server_resp:
    case constants__e_msg_discovery_register_server2_resp:
    case constants__e_msg_service_fault_resp:
        *io_dispatch_mgr__header_type = constants__e_msg_response_type;
        break;
    default:
        break;
    }
}

void io_dispatch_mgr__get_msg_service_class(const constants__t_msg_type_i io_dispatch_mgr__msg_typ,
                                            constants__t_msg_service_class_i* const io_dispatch_mgr__service_class)
{
    switch (io_dispatch_mgr__msg_typ)
    {
    case constants__e_msg_discovery_find_servers_req:
    case constants__e_msg_discovery_find_servers_resp:
    case constants__e_msg_discovery_find_servers_on_network_req:
    case constants__e_msg_discovery_find_servers_on_network_resp:
    case constants__e_msg_discovery_get_endpoints_req:
    case constants__e_msg_discovery_get_endpoints_resp:
    case constants__e_msg_discovery_register_server_req:
    case constants__e_msg_discovery_register_server_resp:
    case constants__e_msg_discovery_register_server2_req:
    case constants__e_msg_discovery_register_server2_resp:
        *io_dispatch_mgr__service_class = constants__e_msg_discovery_service_class;
        break;
    case constants__e_msg_session_create_req:
    case constants__e_msg_session_create_resp:
    case constants__e_msg_session_activate_req:
    case constants__e_msg_session_activate_resp:
    case constants__e_msg_session_close_req:
    case constants__e_msg_session_close_resp:
    case constants__e_msg_session_cancel_req:
    case constants__e_msg_session_cancel_resp:
        *io_dispatch_mgr__service_class = constants__e_msg_session_treatment_class;
        break;
    case constants__e_msg_node_add_nodes_req:
    case constants__e_msg_node_add_nodes_resp:
    case constants__e_msg_node_add_references_req:
    case constants__e_msg_node_add_references_resp:
    case constants__e_msg_node_delete_nodes_req:
    case constants__e_msg_node_delete_nodes_resp:
    case constants__e_msg_node_delete_references_req:
    case constants__e_msg_node_delete_references_resp:
    case constants__e_msg_view_browse_req:
    case constants__e_msg_view_browse_resp:
    case constants__e_msg_view_browse_next_req:
    case constants__e_msg_view_browse_next_resp:
    case constants__e_msg_view_translate_browse_paths_to_node_ids_req:
    case constants__e_msg_view_translate_browse_paths_to_node_ids_resp:
    case constants__e_msg_view_register_nodes_req:
    case constants__e_msg_view_register_nodes_resp:
    case constants__e_msg_view_unregister_nodes_req:
    case constants__e_msg_view_unregister_nodes_resp:
    case constants__e_msg_query_first_req:
    case constants__e_msg_query_first_resp:
    case constants__e_msg_query_next_req:
    case constants__e_msg_query_next_resp:
    case constants__e_msg_attribute_read_req:
    case constants__e_msg_attribute_read_resp:
    case constants__e_msg_attribute_history_read_req:
    case constants__e_msg_attribute_history_read_resp:
    case constants__e_msg_attribute_write_req:
    case constants__e_msg_attribute_write_resp:
    case constants__e_msg_attribute_history_update_req:
    case constants__e_msg_attribute_history_update_resp:
    case constants__e_msg_method_call_req:
    case constants__e_msg_method_call_resp:
    case constants__e_msg_monitored_items_create_req:
    case constants__e_msg_monitored_items_create_resp:
    case constants__e_msg_monitored_items_modify_req:
    case constants__e_msg_monitored_items_modify_resp:
    case constants__e_msg_monitored_items_set_monitoring_mode_req:
    case constants__e_msg_monitored_items_set_monitoring_mode_resp:
    case constants__e_msg_monitored_items_set_triggering_req:
    case constants__e_msg_monitored_items_set_triggering_resp:
    case constants__e_msg_monitored_items_delete_req:
    case constants__e_msg_monitored_items_delete_resp:
    case constants__e_msg_subscription_create_req:
    case constants__e_msg_subscription_create_resp:
    case constants__e_msg_subscription_modify_req:
    case constants__e_msg_subscription_modify_resp:
    case constants__e_msg_subscription_set_publishing_mode_req:
    case constants__e_msg_subscription_set_publishing_mode_resp:
    case constants__e_msg_subscription_publish_req:
    case constants__e_msg_subscription_publish_resp:
    case constants__e_msg_subscription_republish_req:
    case constants__e_msg_subscription_republish_resp:
    case constants__e_msg_subscription_transfer_subscriptions_req:
    case constants__e_msg_subscription_transfer_subscriptions_resp:
    case constants__e_msg_subscription_delete_subscriptions_req:
    case constants__e_msg_subscription_delete_subscriptions_resp:
        *io_dispatch_mgr__service_class = constants__e_msg_session_service_class;
        break;
    case constants__e_msg_service_fault_resp:
        *io_dispatch_mgr__service_class = constants__e_msg_service_fault_class;
        break;
    default:
        *io_dispatch_mgr__service_class = constants__c_msg_service_class_indet;
        break;
    }
}

void io_dispatch_mgr__receive_msg_buffer(const constants__t_channel_i io_dispatch_mgr__channel,
                                         const constants__t_byte_buffer_i io_dispatch_mgr__buffer,
                                         const constants__t_request_context_i io_dispatch_mgr__request_context)
{
    {
        t_bool io_dispatch_mgr__l_connected_channel;
        t_bool io_dispatch_mgr__l_is_client;
        constants__t_msg_type_i io_dispatch_mgr__l_msg_type;
        t_bool io_dispatch_mgr__l_valid_msg_type;
        constants__t_msg_header_type_i io_dispatch_mgr__l_msg_header_type;
        constants__t_msg_service_class_i io_dispatch_mgr__l_msg_service_class;
        constants__t_byte_buffer_i io_dispatch_mgr__l_buffer_out;
        t_bool io_dispatch_mgr__l_valid_buffer_out;
        t_bool io_dispatch_mgr__l_valid_req_context;

        channel_mgr__is_connected_channel(io_dispatch_mgr__channel, &io_dispatch_mgr__l_connected_channel);
        service_mgr__decode_msg_type(io_dispatch_mgr__buffer, &io_dispatch_mgr__l_msg_type);
        service_mgr__is_valid_msg_in_type(io_dispatch_mgr__l_msg_type, &io_dispatch_mgr__l_valid_msg_type);
        if ((io_dispatch_mgr__l_connected_channel == true) && (io_dispatch_mgr__l_valid_msg_type == true))
        {
            channel_mgr__is_client_channel(io_dispatch_mgr__channel, &io_dispatch_mgr__l_is_client);
            io_dispatch_mgr__get_msg_header_type(io_dispatch_mgr__l_msg_type, &io_dispatch_mgr__l_msg_header_type);
            io_dispatch_mgr__get_msg_service_class(io_dispatch_mgr__l_msg_type, &io_dispatch_mgr__l_msg_service_class);
            switch (io_dispatch_mgr__l_msg_header_type)
            {
            case constants__e_msg_request_type:
                service_mgr__is_valid_request_context(io_dispatch_mgr__request_context,
                                                      &io_dispatch_mgr__l_valid_req_context);
                if ((io_dispatch_mgr__l_is_client == false) && (io_dispatch_mgr__l_valid_req_context == true))
                {
                    switch (io_dispatch_mgr__l_msg_service_class)
                    {
                    case constants__e_msg_session_treatment_class:
                        service_mgr__server_receive_session_treatment_req(
                            io_dispatch_mgr__channel, io_dispatch_mgr__l_msg_type, io_dispatch_mgr__buffer,
                            &io_dispatch_mgr__l_buffer_out);
                        break;
                    case constants__e_msg_session_service_class:
                        service_mgr__server_receive_session_service_req(
                            io_dispatch_mgr__channel, io_dispatch_mgr__l_msg_type, io_dispatch_mgr__buffer,
                            &io_dispatch_mgr__l_buffer_out);
                        break;
                    case constants__e_msg_discovery_service_class:
                        service_mgr__server_receive_discovery_service_req(
                            io_dispatch_mgr__channel, io_dispatch_mgr__l_msg_type, io_dispatch_mgr__buffer,
                            &io_dispatch_mgr__l_buffer_out);
                        break;
                    default:
                        io_dispatch_mgr__l_buffer_out = constants__c_byte_buffer_indet;
                        break;
                    }
                    service_mgr__is_valid_buffer_out(io_dispatch_mgr__l_buffer_out,
                                                     &io_dispatch_mgr__l_valid_buffer_out);
                    if (io_dispatch_mgr__l_valid_buffer_out == true)
                    {
                        channel_mgr__send_channel_msg_buffer(io_dispatch_mgr__channel, io_dispatch_mgr__l_buffer_out,
                                                             io_dispatch_mgr__request_context);
                    }
                }
                else
                {
                    channel_mgr__close_secure_channel(io_dispatch_mgr__channel);
                }
                break;
            case constants__e_msg_response_type:
                if (io_dispatch_mgr__l_is_client == true)
                {
                    switch (io_dispatch_mgr__l_msg_service_class)
                    {
                    case constants__e_msg_session_treatment_class:
                        service_mgr__client_receive_session_treatment_resp(
                            io_dispatch_mgr__channel, io_dispatch_mgr__l_msg_type, io_dispatch_mgr__buffer);
                        break;
                    case constants__e_msg_session_service_class:
                        service_mgr__client_receive_session_service_resp(
                            io_dispatch_mgr__channel, io_dispatch_mgr__l_msg_type, io_dispatch_mgr__buffer);
                        break;
                    case constants__e_msg_discovery_service_class:
                        service_mgr__client_receive_discovery_service_resp(io_dispatch_mgr__l_msg_type,
                                                                           io_dispatch_mgr__buffer);
                        break;
                    case constants__e_msg_service_fault_class:;
                        break;
                    default:
                        break;
                    }
                }
                else
                {
                    channel_mgr__close_secure_channel(io_dispatch_mgr__channel);
                }
                break;
            default:
                channel_mgr__close_secure_channel(io_dispatch_mgr__channel);
                break;
            }
        }
    }
}

void io_dispatch_mgr__snd_msg_failure(const constants__t_channel_i io_dispatch_mgr__channel,
                                      const constants__t_request_context_i io_dispatch_mgr__request_id,
                                      const constants__t_StatusCode_i io_dispatch_mgr__error_status)
{
    {
        t_bool io_dispatch_mgr__l_connected_channel;
        t_bool io_dispatch_mgr__l_is_client_channel;
        constants__t_request_handle_i io_dispatch_mgr__l_request_handle;

        channel_mgr__is_connected_channel(io_dispatch_mgr__channel, &io_dispatch_mgr__l_connected_channel);
        if (io_dispatch_mgr__l_connected_channel == true)
        {
            channel_mgr__is_client_channel(io_dispatch_mgr__channel, &io_dispatch_mgr__l_is_client_channel);
            if (io_dispatch_mgr__l_is_client_channel == true)
            {
                service_mgr__client_request_id_to_req_handle(io_dispatch_mgr__request_id,
                                                             &io_dispatch_mgr__l_request_handle);
                service_mgr__client_snd_msg_failure(io_dispatch_mgr__channel, io_dispatch_mgr__l_request_handle,
                                                    io_dispatch_mgr__error_status);
            }
        }
    }
}

void io_dispatch_mgr__client_channel_connected_event(
    const constants__t_channel_config_idx_i io_dispatch_mgr__channel_config_idx,
    const constants__t_channel_i io_dispatch_mgr__channel)
{
    {
        t_bool io_dispatch_mgr__l_bres;

        channel_mgr__cli_set_connected_channel(io_dispatch_mgr__channel_config_idx, io_dispatch_mgr__channel,
                                               &io_dispatch_mgr__l_bres);
        if (io_dispatch_mgr__l_bres == true)
        {
            service_mgr__client_channel_connected_event_session(io_dispatch_mgr__channel_config_idx,
                                                                io_dispatch_mgr__channel);
            service_mgr__client_channel_connected_event_discovery(io_dispatch_mgr__channel_config_idx,
                                                                  io_dispatch_mgr__channel);
        }
    }
}

void io_dispatch_mgr__client_secure_channel_timeout(
    const constants__t_channel_config_idx_i io_dispatch_mgr__channel_config_idx)
{
    {
        t_bool io_dispatch_mgr__l_bres;

        channel_mgr__cli_set_connection_timeout_channel(io_dispatch_mgr__channel_config_idx, &io_dispatch_mgr__l_bres);
    }
}

void io_dispatch_mgr__server_channel_connected_event(
    const constants__t_endpoint_config_idx_i io_dispatch_mgr__endpoint_config_idx,
    const constants__t_channel_config_idx_i io_dispatch_mgr__channel_config_idx,
    const constants__t_channel_i io_dispatch_mgr__channel,
    t_bool* const io_dispatch_mgr__bres)
{
    channel_mgr__srv_new_secure_channel(io_dispatch_mgr__endpoint_config_idx, io_dispatch_mgr__channel_config_idx,
                                        io_dispatch_mgr__channel, io_dispatch_mgr__bres);
}

void io_dispatch_mgr__client_activate_new_session(
    const constants__t_channel_config_idx_i io_dispatch_mgr__channel_config_idx,
    const constants__t_user_i io_dispatch_mgr__user,
    const constants__t_application_context_i io_dispatch_mgr__app_context,
    t_bool* const io_dispatch_mgr__bres)
{
    {
        constants__t_channel_i io_dispatch_mgr__l_channel;
        t_bool io_dispatch_mgr__l_connected_channel;

        channel_mgr__is_valid_channel_config_idx(io_dispatch_mgr__channel_config_idx, io_dispatch_mgr__bres);
        if (*io_dispatch_mgr__bres == true)
        {
            channel_mgr__get_connected_channel(io_dispatch_mgr__channel_config_idx, &io_dispatch_mgr__l_channel);
            channel_mgr__is_connected_channel(io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_connected_channel);
            if (io_dispatch_mgr__l_connected_channel == false)
            {
                channel_mgr__cli_open_secure_channel(io_dispatch_mgr__channel_config_idx, io_dispatch_mgr__bres);
                if (*io_dispatch_mgr__bres == true)
                {
                    service_mgr__client_async_activate_new_session_without_channel(
                        io_dispatch_mgr__channel_config_idx, io_dispatch_mgr__user, io_dispatch_mgr__app_context,
                        io_dispatch_mgr__bres);
                }
            }
            else
            {
                service_mgr__client_async_activate_new_session_with_channel(
                    io_dispatch_mgr__channel_config_idx, io_dispatch_mgr__l_channel, io_dispatch_mgr__user,
                    io_dispatch_mgr__app_context, io_dispatch_mgr__bres);
            }
        }
    }
}

void io_dispatch_mgr__client_reactivate_session_new_user(const constants__t_session_i io_dispatch_mgr__session,
                                                         const constants__t_user_i io_dispatch_mgr__user)
{
    {
        t_bool io_dispatch_mgr__l_valid_session;
        constants__t_StatusCode_i io_dispatch_mgr__l_ret;
        constants__t_channel_i io_dispatch_mgr__l_channel;
        t_bool io_dispatch_mgr__l_connected_channel;
        constants__t_byte_buffer_i io_dispatch_mgr__l_buffer_out;
        t_bool io_dispatch_mgr__l_valid_buffer_out;
        constants__t_request_handle_i io_dispatch_mgr__l_req_handle;
        constants__t_request_context_i io_dispatch_mgr__l_req_handle_in_req_id;

        service_mgr__is_valid_session(io_dispatch_mgr__session, &io_dispatch_mgr__l_valid_session);
        if (io_dispatch_mgr__l_valid_session == true)
        {
            service_mgr__client_service_activate_session(
                io_dispatch_mgr__session, io_dispatch_mgr__user, &io_dispatch_mgr__l_ret, &io_dispatch_mgr__l_channel,
                &io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_req_handle);
            if (io_dispatch_mgr__l_ret == constants__e_sc_ok)
            {
                channel_mgr__is_connected_channel(io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_connected_channel);
                service_mgr__is_valid_buffer_out(io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_valid_buffer_out);
                if ((io_dispatch_mgr__l_connected_channel == true) && (io_dispatch_mgr__l_valid_buffer_out == true))
                {
                    service_mgr__client_req_handle_to_request_id(io_dispatch_mgr__l_req_handle,
                                                                 &io_dispatch_mgr__l_req_handle_in_req_id);
                    channel_mgr__send_channel_msg_buffer(io_dispatch_mgr__l_channel, io_dispatch_mgr__l_buffer_out,
                                                         io_dispatch_mgr__l_req_handle_in_req_id);
                }
            }
        }
    }
}

void io_dispatch_mgr__client_send_service_request(const constants__t_session_i io_dispatch_mgr__session,
                                                  const constants__t_msg_i io_dispatch_mgr__req_msg,
                                                  const constants__t_application_context_i io_dispatch_mgr__app_context,
                                                  constants__t_StatusCode_i* const io_dispatch_mgr__ret)
{
    {
        t_bool io_dispatch_mgr__l_valid_session;
        t_bool io_dispatch_mgr__l_valid_msg;
        constants__t_channel_i io_dispatch_mgr__l_channel;
        t_bool io_dispatch_mgr__l_connected_channel;
        constants__t_byte_buffer_i io_dispatch_mgr__l_buffer_out;
        t_bool io_dispatch_mgr__l_valid_buffer_out;
        constants__t_request_handle_i io_dispatch_mgr__l_req_handle;
        constants__t_request_context_i io_dispatch_mgr__l_req_handle_in_req_id;

        service_mgr__is_valid_session(io_dispatch_mgr__session, &io_dispatch_mgr__l_valid_session);
        service_mgr__is_valid_app_msg_out(io_dispatch_mgr__req_msg, &io_dispatch_mgr__l_valid_msg);
        if ((io_dispatch_mgr__l_valid_session == true) && (io_dispatch_mgr__l_valid_msg == true))
        {
            service_mgr__client_service_request(
                io_dispatch_mgr__session, io_dispatch_mgr__req_msg, io_dispatch_mgr__app_context, io_dispatch_mgr__ret,
                &io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_req_handle);
            if (*io_dispatch_mgr__ret == constants__e_sc_ok)
            {
                channel_mgr__is_connected_channel(io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_connected_channel);
                service_mgr__is_valid_buffer_out(io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_valid_buffer_out);
                if ((io_dispatch_mgr__l_connected_channel == true) && (io_dispatch_mgr__l_valid_buffer_out == true))
                {
                    service_mgr__client_req_handle_to_request_id(io_dispatch_mgr__l_req_handle,
                                                                 &io_dispatch_mgr__l_req_handle_in_req_id);
                    channel_mgr__send_channel_msg_buffer(io_dispatch_mgr__l_channel, io_dispatch_mgr__l_buffer_out,
                                                         io_dispatch_mgr__l_req_handle_in_req_id);
                }
            }
        }
        else
        {
            *io_dispatch_mgr__ret = constants__e_sc_bad_invalid_argument;
            if (io_dispatch_mgr__l_valid_msg == true)
            {
                service_mgr__bless_msg_out(io_dispatch_mgr__req_msg);
                service_mgr__dealloc_msg_out(io_dispatch_mgr__req_msg);
            }
        }
    }
}

void io_dispatch_mgr__client_send_discovery_request(
    const constants__t_channel_config_idx_i io_dispatch_mgr__channel_config_idx,
    const constants__t_msg_i io_dispatch_mgr__req_msg,
    const constants__t_application_context_i io_dispatch_mgr__app_context,
    constants__t_StatusCode_i* const io_dispatch_mgr__ret)
{
    {
        t_bool io_dispatch_mgr__l_valid_msg;
        t_bool io_dispatch_mgr__l_valid_channel_config;
        t_bool io_dispatch_mgr__l_bres;
        constants__t_channel_i io_dispatch_mgr__l_channel;
        t_bool io_dispatch_mgr__l_connected_channel;
        constants__t_byte_buffer_i io_dispatch_mgr__l_buffer_out;
        constants__t_request_handle_i io_dispatch_mgr__l_req_handle;
        constants__t_request_context_i io_dispatch_mgr__l_req_handle_in_req_id;

        service_mgr__is_valid_app_msg_out(io_dispatch_mgr__req_msg, &io_dispatch_mgr__l_valid_msg);
        channel_mgr__is_valid_channel_config_idx(io_dispatch_mgr__channel_config_idx,
                                                 &io_dispatch_mgr__l_valid_channel_config);
        if ((io_dispatch_mgr__l_valid_msg == true) && (io_dispatch_mgr__l_valid_channel_config == true))
        {
            channel_mgr__get_connected_channel(io_dispatch_mgr__channel_config_idx, &io_dispatch_mgr__l_channel);
            channel_mgr__is_connected_channel(io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_connected_channel);
            if (io_dispatch_mgr__l_connected_channel == false)
            {
                channel_mgr__cli_open_secure_channel(io_dispatch_mgr__channel_config_idx, &io_dispatch_mgr__l_bres);
                if (io_dispatch_mgr__l_bres == true)
                {
                    service_mgr__client_async_discovery_request_without_channel(
                        io_dispatch_mgr__channel_config_idx, io_dispatch_mgr__req_msg, io_dispatch_mgr__app_context,
                        &io_dispatch_mgr__l_bres);
                    if (io_dispatch_mgr__l_bres == true)
                    {
                        *io_dispatch_mgr__ret = constants__e_sc_ok;
                    }
                    else
                    {
                        service_mgr__bless_msg_out(io_dispatch_mgr__req_msg);
                        service_mgr__dealloc_msg_out(io_dispatch_mgr__req_msg);
                        *io_dispatch_mgr__ret = constants__e_sc_bad_too_many_ops;
                    }
                }
                else
                {
                    *io_dispatch_mgr__ret = constants__e_sc_bad_generic;
                }
            }
            else
            {
                service_mgr__client_discovery_service_request(io_dispatch_mgr__req_msg, io_dispatch_mgr__app_context,
                                                              io_dispatch_mgr__ret, &io_dispatch_mgr__l_buffer_out,
                                                              &io_dispatch_mgr__l_req_handle);
                if (*io_dispatch_mgr__ret == constants__e_sc_ok)
                {
                    service_mgr__client_req_handle_to_request_id(io_dispatch_mgr__l_req_handle,
                                                                 &io_dispatch_mgr__l_req_handle_in_req_id);
                    channel_mgr__send_channel_msg_buffer(io_dispatch_mgr__l_channel, io_dispatch_mgr__l_buffer_out,
                                                         io_dispatch_mgr__l_req_handle_in_req_id);
                }
            }
        }
        else
        {
            *io_dispatch_mgr__ret = constants__e_sc_bad_invalid_argument;
            if (io_dispatch_mgr__l_valid_msg == true)
            {
                service_mgr__bless_msg_out(io_dispatch_mgr__req_msg);
                service_mgr__dealloc_msg_out(io_dispatch_mgr__req_msg);
            }
        }
    }
}

void io_dispatch_mgr__client_send_close_session_request(const constants__t_session_i io_dispatch_mgr__session,
                                                        constants__t_StatusCode_i* const io_dispatch_mgr__ret)
{
    {
        t_bool io_dispatch_mgr__l_valid_session;
        constants__t_channel_i io_dispatch_mgr__l_channel;
        t_bool io_dispatch_mgr__l_connected_channel;
        constants__t_byte_buffer_i io_dispatch_mgr__l_buffer_out;
        t_bool io_dispatch_mgr__l_valid_buffer_out;
        constants__t_request_handle_i io_dispatch_mgr__l_req_handle;
        constants__t_request_context_i io_dispatch_mgr__l_req_handle_in_req_id;

        service_mgr__is_valid_session(io_dispatch_mgr__session, &io_dispatch_mgr__l_valid_session);
        if (io_dispatch_mgr__l_valid_session == true)
        {
            service_mgr__client_service_close_session(io_dispatch_mgr__session, io_dispatch_mgr__ret,
                                                      &io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_buffer_out,
                                                      &io_dispatch_mgr__l_req_handle);
            if (*io_dispatch_mgr__ret == constants__e_sc_ok)
            {
                channel_mgr__is_connected_channel(io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_connected_channel);
                service_mgr__is_valid_buffer_out(io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_valid_buffer_out);
                if ((io_dispatch_mgr__l_connected_channel == true) && (io_dispatch_mgr__l_valid_buffer_out == true))
                {
                    service_mgr__client_req_handle_to_request_id(io_dispatch_mgr__l_req_handle,
                                                                 &io_dispatch_mgr__l_req_handle_in_req_id);
                    channel_mgr__send_channel_msg_buffer(io_dispatch_mgr__l_channel, io_dispatch_mgr__l_buffer_out,
                                                         io_dispatch_mgr__l_req_handle_in_req_id);
                }
            }
        }
        else
        {
            *io_dispatch_mgr__ret = constants__e_sc_bad_invalid_argument;
        }
    }
}

void io_dispatch_mgr__internal_client_create_session(
    const constants__t_session_i io_dispatch_mgr__session,
    const constants__t_channel_config_idx_i io_dispatch_mgr__channel_config_idx)
{
    {
        constants__t_channel_i io_dispatch_mgr__l_channel;
        t_bool io_dispatch_mgr__l_connected_channel;
        constants__t_byte_buffer_i io_dispatch_mgr__l_buffer_out;
        t_bool io_dispatch_mgr__l_valid_buffer_out;
        constants__t_request_handle_i io_dispatch_mgr__l_req_handle;
        constants__t_request_context_i io_dispatch_mgr__l_req_handle_in_req_id;

        channel_mgr__get_connected_channel(io_dispatch_mgr__channel_config_idx, &io_dispatch_mgr__l_channel);
        channel_mgr__is_connected_channel(io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_connected_channel);
        if (io_dispatch_mgr__l_connected_channel == false)
        {
            service_mgr__client_close_session(io_dispatch_mgr__session);
        }
        else
        {
            service_mgr__client_service_create_session(io_dispatch_mgr__session, io_dispatch_mgr__l_channel,
                                                       &io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_req_handle);
            service_mgr__is_valid_buffer_out(io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_valid_buffer_out);
            if (io_dispatch_mgr__l_valid_buffer_out == true)
            {
                service_mgr__client_req_handle_to_request_id(io_dispatch_mgr__l_req_handle,
                                                             &io_dispatch_mgr__l_req_handle_in_req_id);
                channel_mgr__send_channel_msg_buffer(io_dispatch_mgr__l_channel, io_dispatch_mgr__l_buffer_out,
                                                     io_dispatch_mgr__l_req_handle_in_req_id);
            }
        }
    }
}

void io_dispatch_mgr__internal_client_activate_orphaned_session(
    const constants__t_session_i io_dispatch_mgr__session,
    const constants__t_channel_config_idx_i io_dispatch_mgr__channel_config_idx)
{
    {
        constants__t_channel_i io_dispatch_mgr__l_channel;
        t_bool io_dispatch_mgr__l_connected_channel;
        constants__t_byte_buffer_i io_dispatch_mgr__l_buffer_out;
        t_bool io_dispatch_mgr__l_valid_buffer_out;
        constants__t_request_handle_i io_dispatch_mgr__l_req_handle;
        constants__t_request_context_i io_dispatch_mgr__l_req_handle_in_req_id;

        channel_mgr__get_connected_channel(io_dispatch_mgr__channel_config_idx, &io_dispatch_mgr__l_channel);
        channel_mgr__is_connected_channel(io_dispatch_mgr__l_channel, &io_dispatch_mgr__l_connected_channel);
        if (io_dispatch_mgr__l_connected_channel == false)
        {
            service_mgr__client_service_activate_orphaned_session(io_dispatch_mgr__session, io_dispatch_mgr__l_channel,
                                                                  &io_dispatch_mgr__l_buffer_out,
                                                                  &io_dispatch_mgr__l_req_handle);
            service_mgr__is_valid_buffer_out(io_dispatch_mgr__l_buffer_out, &io_dispatch_mgr__l_valid_buffer_out);
            if (io_dispatch_mgr__l_valid_buffer_out == true)
            {
                service_mgr__client_req_handle_to_request_id(io_dispatch_mgr__l_req_handle,
                                                             &io_dispatch_mgr__l_req_handle_in_req_id);
                channel_mgr__send_channel_msg_buffer(io_dispatch_mgr__l_channel, io_dispatch_mgr__l_buffer_out,
                                                     io_dispatch_mgr__l_req_handle_in_req_id);
            }
        }
    }
}

void io_dispatch_mgr__secure_channel_lost(const constants__t_channel_i io_dispatch_mgr__channel)
{
    {
        t_bool io_dispatch_mgr__l_connected_channel;
        t_bool io_dispatch_mgr__l_disconnecting_channel;
        t_bool io_dispatch_mgr__l_valid_new_channel;
        t_bool io_dispatch_mgr__l_is_client;
        constants__t_channel_config_idx_i io_dispatch_mgr__l_channel_config_idx;
        constants__t_channel_i io_dispatch_mgr__l_new_channel;
        t_bool io_dispatch_mgr__l_bres;

        channel_mgr__is_connected_channel(io_dispatch_mgr__channel, &io_dispatch_mgr__l_connected_channel);
        if (io_dispatch_mgr__l_connected_channel == true)
        {
            channel_mgr__is_client_channel(io_dispatch_mgr__channel, &io_dispatch_mgr__l_is_client);
            if (io_dispatch_mgr__l_is_client == true)
            {
                channel_mgr__get_channel_info(io_dispatch_mgr__channel, &io_dispatch_mgr__l_channel_config_idx);
                channel_mgr__is_disconnecting_channel(io_dispatch_mgr__l_channel_config_idx,
                                                      &io_dispatch_mgr__l_disconnecting_channel);
                service_mgr__client_secure_channel_lost_session_sm(io_dispatch_mgr__channel,
                                                                   io_dispatch_mgr__l_channel_config_idx);
                if (io_dispatch_mgr__l_disconnecting_channel == false)
                {
                    channel_mgr__get_connected_channel(io_dispatch_mgr__l_channel_config_idx,
                                                       &io_dispatch_mgr__l_new_channel);
                    if (io_dispatch_mgr__l_new_channel == constants__c_channel_indet)
                    {
                        channel_mgr__cli_open_secure_channel(io_dispatch_mgr__l_channel_config_idx,
                                                             &io_dispatch_mgr__l_bres);
                    }
                    channel_mgr__is_connected_channel(io_dispatch_mgr__l_new_channel,
                                                      &io_dispatch_mgr__l_valid_new_channel);
                    if (io_dispatch_mgr__l_valid_new_channel == true)
                    {
                        service_mgr__client_channel_connected_event_session(io_dispatch_mgr__l_channel_config_idx,
                                                                            io_dispatch_mgr__l_new_channel);
                    }
                }
            }
            else
            {
                service_mgr__server_secure_channel_lost_session_sm(io_dispatch_mgr__channel);
            }
            channel_mgr__channel_lost(io_dispatch_mgr__channel);
        }
    }
}

void io_dispatch_mgr__close_all_active_connections(t_bool* const io_dispatch_mgr__bres)
{
    channel_mgr__close_all_channel(io_dispatch_mgr__bres);
}
