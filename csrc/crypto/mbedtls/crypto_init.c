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

#include "crypto_init.h"

#include <mbedtls/config.h>
#include <stdlib.h>

#include "sopc_mutexes.h"

#ifdef MBEDTLS_THREADING_ALT
#include <mbedtls/threading.h>
#endif

Once mutex_impl_once = ONCE_STATIC_INIT;

#if defined(MBEDTLS_THREADING_ALT)
static void mutex_init(mbedtls_threading_mutex_t* mutex)
{
    if (mutex == NULL || mutex->valid)
    {
        return;
    }

    mutex->mutex = calloc(1, sizeof(Mutex));

    if (mutex->mutex == NULL)
    {
        return;
    }

    if (Mutex_Initialization((Mutex*) mutex->mutex) == SOPC_STATUS_OK)
    {
        mutex->valid = 1;
    }
}

static void mutex_free(mbedtls_threading_mutex_t* mutex)
{
    if (mutex == NULL)
    {
        return;
    }

    if (mutex->valid)
    {
        Mutex_Clear(mutex->mutex);
    }

    free(mutex->mutex);
    mutex->mutex = NULL;
    mutex->valid = 0;
}

static int mutex_lock(mbedtls_threading_mutex_t* mutex)
{
    if (mutex == NULL || !mutex->valid)
    {
        return MBEDTLS_ERR_THREADING_BAD_INPUT_DATA;
    }

    return (Mutex_Lock(mutex->mutex) == SOPC_STATUS_OK) ? 0 : MBEDTLS_ERR_THREADING_MUTEX_ERROR;
}

static int mutex_unlock(mbedtls_threading_mutex_t* mutex)
{
    if (mutex == NULL || !mutex->valid)
    {
        return MBEDTLS_ERR_THREADING_BAD_INPUT_DATA;
    }

    return (Mutex_Unlock(mutex->mutex) == SOPC_STATUS_OK) ? 0 : MBEDTLS_ERR_THREADING_MUTEX_ERROR;
}

static void init_mbedtls_mutex_impl(void)
{
    mbedtls_threading_set_alt(mutex_init, mutex_free, mutex_lock, mutex_unlock);
}
#elif defined(MBEDTLS_THREADING_PTHREAD)
static void init_mbedtls_mutex_impl(void) {}
#else
#error "Unsupported MbedTLS threading implementation"
#endif

void SOPC_MbedTLS_Init(void)
{
    DoOnce(&mutex_impl_once, init_mbedtls_mutex_impl);
}
