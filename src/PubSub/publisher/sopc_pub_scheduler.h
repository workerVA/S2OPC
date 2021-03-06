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

#ifndef SOPC_PUB_SCHEDULER_H_
#define SOPC_PUB_SCHEDULER_H_

#include "sopc_pub_source_variable.h"
#include "sopc_pubsub_conf.h"

#ifndef SOPC_PUBSCHEDULER_HEARTBEAT_FROM_IRQ
#define SOPC_PUBSCHEDULER_HEARTBEAT_FROM_IRQ 0
#endif

/**
 * \brief Starts the Publisher scheduler using the PubSub configuration data
 *        and the source of data information
 *
 * \param config              The PubSub configuration to be used to start the Publisher
 * \param sourceConfig        The source configured to retrieve up to date data referenced in \p config
 * \param resolutionMicroSecs The time resolution in micro seconds to use to evaluate publishing intervals periods.
 *                            In case hardware interruption is used with SOPC_PubScheduler_HeartBeatFromIRQ,
 *                            this parameter value shall be the tick resolution that will be used to call it
 *                            and increment tickValue.
 *                            Otherwise it will be the minimum time between 2 publishing intervals period evaluation
 *                            (in this case minimum value is 1 millisecond, replaced by if needed).
 *
 * \note \p resolutionMicroSecs shall be less than any PublishingInterval configured,
 *       otherwise PublishingInterval configuration is replaced by \p resolutionMicroSecs.
 */
bool SOPC_PubScheduler_Start(SOPC_PubSubConfiguration* config,
                             SOPC_PubSourceVariableConfig* sourceConfig,
                             uint32_t resolutionMicroSecs);

void SOPC_PubScheduler_Stop(void);

#if SOPC_PUBSCHEDULER_HEARTBEAT_FROM_IRQ == 1
// tickValue shall be incremented by 1 exactly each \p resolutionMicroSecs micro seconds
SOPC_ReturnStatus SOPC_PubScheduler_HeartBeatFromIRQ(uint32_t tickValue);
#endif

#endif /* SOPC_PUB_SCHEDULER_H_ */
