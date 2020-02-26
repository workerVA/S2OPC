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

#include <stdlib.h>

/* Zephyr includes */

#include "kernel.h"

/* s2opc includes */

#include "sopc_enums.h"

/* platform dep includes */

#include "p_synchro.h"

/* Flag bit used into status uint32 value to indicates that quit request is on going */

#define MASK_SET_QUIT_FLAG (0x80000000)

// *** Private enumeration definition ***

// Mutex or condition variable status
typedef enum E_SYNCHRO_STATUS
{
    E_SYNC_STATUS_NOT_INITIALIZED, // Condition / Mutex variable not initialized
    E_SYNC_STATUS_INITIALIZING,    // Condition / Mutex variable initializing
    E_SYNC_STATUS_DEINITIALIZING,  // Condition / Mutex variable de initializing
    E_SYNC_STATUS_INITIALIZED,     // Condition / Mutex variable initialized
    E_SYNC_STATUS_SIZE = INT32_MAX
} eSyncStatus;

// *** Private object definition ***

// Signal status used by condition variable
typedef enum E_SIG_STATUS
{
    E_SIG_STATUS_NOT_RESERVED,    // Signal free to use
    E_SIG_STATUS_RESERVING,       // Signal reserving
    E_SIG_STATUS_WAIT_FOR_SIGNAL, // Signal waiting
    E_SIG_STATUS_SIZE = INT32_MAX
} eSigStatus;

// Signal object definition
typedef struct tSignal
{
    volatile eSigStatus sigStatus; // Signal status
    struct k_sem signal;           // Signal (semaphore object)
} tSignal;

// Condition variable object definition
typedef struct tCondVar
{
    volatile eSyncStatus status;              // Condition variable status
    tSignal tabSignals[MAX_COND_VAR_WAITERS]; // Table of signals
} tCondVar;

// Mutex variable object definition
typedef struct tMutVar
{
    volatile eSyncStatus status; // Mutex status
    tCondVarHandle condVarHdl;   // Handle of condition variable
    uint32_t lockCounter;        // Lock counter
    k_tid_t ownerThread;         // Mutex ownwer thread
    struct k_mutex lock;         // Kernel mutex
} tMutVar;

// *** Private workspace definition, preallocated condition variables and mutex ***

// Condition variables workspace, handle table of condition variables
static struct tCondVarWks
{
    struct tCondVar tabWks[MAX_COND_VAR];
} gCondVarWks;

// Mutex variables workspace, handle table of mutex variables
static struct tMutVarWks
{
    struct tMutVar tabWks[MAX_MUT_VAR];
} gMutVarWks;

// *** Private functions declarations ***

// Modify atomically status of condition variable : set flag quit,
// increment / decrement status from initialized status
static inline eSyncStatus P_SYNCHRO_Condition_Set_Quit_Flag(tCondVar* p);   // Initiate clear operation
static inline eSyncStatus P_SYNCHRO_Condition_Add_Api_User(tCondVar* p);    // Increment in use counter
static inline eSyncStatus P_SYNCHRO_Condition_Remove_Api_User(tCondVar* p); // Decrement in use counter

static inline eSyncStatus P_SYNCHRO_Mutex_Remove_Api_User(tMutVar* p); // Decrement in use counter
static inline eSyncStatus P_SYNCHRO_Mutex_Add_Api_User(tMutVar* p);    // Increment in use counter
static inline eSyncStatus P_SYNCHRO_Mutex_Set_Quit_Flag(tMutVar* p);   // Initiate clear operation

// *** Internal functions definitions for P_SYNCHRO_CONDITION API ***

// Initialize condition variable
// Returns condition variable handle. If not successful, UINT32_MAX returned.
tCondVarHandle P_SYNCHRO_CONDITION_Initialize(void)
{
    eSynchroResult result = E_SYNCHRO_RESULT_OK;

    uint32_t slotId = UINT32_MAX;

    // Search for not initialized condition variable
    for (uint32_t i = 0; i < MAX_COND_VAR; i++)
    {
        {
            // Try to mark as initializing from not initialized
            eSyncStatus expectedStatus = E_SYNC_STATUS_NOT_INITIALIZED;
            eSyncStatus desiredStatus = E_SYNC_STATUS_INITIALIZING;
            bool bTransition = __atomic_compare_exchange(&gCondVarWks.tabWks[i].status, //
                                                         &expectedStatus,               //
                                                         &desiredStatus,                //
                                                         false,                         //
                                                         __ATOMIC_SEQ_CST,              //
                                                         __ATOMIC_SEQ_CST);             //

            if (bTransition)
            {
                slotId = i;
                break;
            }
        }
    }

    // If slot found, slotId < MAX_COND_VAR
    if (slotId >= MAX_COND_VAR)
    {
        result = E_SYNCHRO_RESULT_NOK;
    }

    // If slot found, get cond var object and init signal
    // then mark it as initialized
    if (E_SYNCHRO_RESULT_OK == result)
    {
        tCondVar* p = &gCondVarWks.tabWks[slotId];
        for (uint32_t i = 0; i < MAX_COND_VAR_WAITERS; i++)
        {
            k_sem_init(&p->tabSignals[i].signal, 0, 1);
        }

        eSyncStatus desiredStatus = E_SYNC_STATUS_INITIALIZED;
        __atomic_store(&p->status, &desiredStatus, __ATOMIC_SEQ_CST);
    }

    return slotId;
}

// Signal all thread waiting on this condition varibale
// Returns : ok if at least one thread is waiting on. Else no_waiters. Nok if invalid state.
eSynchroResult P_SYNCHRO_CONDITION_SignalAll(tCondVarHandle slotId) // handle returned by initialize
{
    eSynchroResult result = E_SYNCHRO_RESULT_NO_WAITERS;

    if (slotId >= MAX_COND_VAR)
    {
        return E_SYNCHRO_RESULT_INVALID_PARAMETERS;
    }

    tCondVar* p = &gCondVarWks.tabWks[slotId];

    // Test de-initializing flag. if set, avoid new API call. Return NOK if set.
    eSyncStatus readStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    __atomic_load(&p->status, &readStatus, __ATOMIC_SEQ_CST);
    if ((readStatus & MASK_SET_QUIT_FLAG) != 0)
    {
        result = E_SYNCHRO_RESULT_NOK;
    }

    // If result not modified, verify if some thread are waiting for signal.
    if (E_SYNCHRO_RESULT_NO_WAITERS == result)
    {
        eSyncStatus newStatus = P_SYNCHRO_Condition_Add_Api_User(p);
        if ((newStatus & ~MASK_SET_QUIT_FLAG) > E_SYNC_STATUS_INITIALIZED)
        {
            eSigStatus readSignal = E_SIG_STATUS_NOT_RESERVED;
            for (uint32_t i = 0; i < MAX_COND_VAR_WAITERS; i++)
            {
                // If signal is waiting state, send signal
                __atomic_load(&p->tabSignals[i].sigStatus, &readSignal, __ATOMIC_SEQ_CST);
                if (E_SIG_STATUS_WAIT_FOR_SIGNAL == readSignal)
                {
                    k_sem_give(&p->tabSignals[i].signal);
                    result = E_SYNCHRO_RESULT_OK;
                }
            }

            P_SYNCHRO_Condition_Remove_Api_User(p);
        }
        else
        {
            result = E_SYNCHRO_RESULT_NOK;
        }
    }

    return result;
}

// Unlock a generic object and wait for a condition variable
eSynchroResult P_SYNCHRO_CONDITION_UnlockAndWait(tCondVarHandle slotId, // Handle of condition variable object
                                                 void* pMutex,          // Generic mutex
                                                 pLockCb cbLock,        // Generic lock
                                                 pUnlockCb cbUnlock,    // Generic unlock
                                                 uint32_t timeoutMs)    // Timeout
{
    eSynchroResult result = E_SYNCHRO_RESULT_OK;

    if (slotId >= MAX_COND_VAR)
    {
        return E_SYNCHRO_RESULT_INVALID_PARAMETERS;
    }

    tCondVar* p = &gCondVarWks.tabWks[slotId];

    eSyncStatus readStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    __atomic_load(&p->status, &readStatus, __ATOMIC_SEQ_CST);
    // Check if quit flag is set. If set, return NOK.
    if ((readStatus & MASK_SET_QUIT_FLAG) != 0)
    {
        result = E_SYNCHRO_RESULT_NOK;
    }

    // If result not modified, search free pre allocated signal and set it as reserving.
    if (E_SYNCHRO_RESULT_OK == result)
    {
        eSyncStatus newStatus = P_SYNCHRO_Condition_Add_Api_User(p);
        if (((newStatus & ~MASK_SET_QUIT_FLAG) > E_SYNC_STATUS_INITIALIZED))
        {
            bool bTransition = false;
            uint32_t signalId = 0;

            for (uint32_t i = 0; i < MAX_COND_VAR_WAITERS && !bTransition; i++)
            {
                {
                    eSigStatus expectedStatus = E_SIG_STATUS_NOT_RESERVED;
                    eSigStatus desiredStatus = E_SIG_STATUS_RESERVING;
                    bTransition = __atomic_compare_exchange(&p->tabSignals[i].sigStatus, //
                                                            &expectedStatus,             //
                                                            &desiredStatus,              //
                                                            false,                       //
                                                            __ATOMIC_SEQ_CST,            //
                                                            __ATOMIC_SEQ_CST);           //
                }
                signalId = i;
            }

            // Check for transition. If failed, no free signal.
            if (bTransition)
            {
                k_sem_reset(&p->tabSignals[signalId].signal);

                // Mark signal as ready to be signaled.
                eSigStatus sigStatus = E_SIG_STATUS_WAIT_FOR_SIGNAL;
                __atomic_store(&p->tabSignals[signalId].sigStatus, //
                               &sigStatus,                         //
                               __ATOMIC_SEQ_CST);                  //

                // Unlock generic mutex.
                if (cbUnlock != NULL && pMutex != NULL)
                {
                    cbUnlock(pMutex);
                }

                // Wait for signal
                int sem_take_res = 0; // Used to check timeout.

                if (UINT32_MAX == timeoutMs)
                {
                    sem_take_res = k_sem_take(&p->tabSignals[signalId].signal, K_FOREVER);
                }
                else
                {
                    sem_take_res = k_sem_take(&p->tabSignals[signalId].signal, K_MSEC(timeoutMs));
                }

                // Mark signal as not reserved
                sigStatus = E_SIG_STATUS_NOT_RESERVED;
                __atomic_store(&p->tabSignals[signalId].sigStatus, //
                               &sigStatus,                         //
                               __ATOMIC_SEQ_CST);                  //

                // Re lock generic mutex
                if (cbLock != NULL && pMutex != NULL)
                {
                    cbLock(pMutex);
                }

                // Check if quit flag is setted. If set, result NOK.
                readStatus = E_SYNC_STATUS_NOT_INITIALIZED;
                __atomic_load(&p->status, &readStatus, __ATOMIC_SEQ_CST);
                // Check if quit flag is set. If set, return NOK.
                if ((readStatus & MASK_SET_QUIT_FLAG) != 0)
                {
                    result = E_SYNCHRO_RESULT_NOK;
                }
                else
                {
                    // Check for received signal
                    if (sem_take_res != 0)
                    {
                        result = E_SYNCHRO_RESULT_TMO;
                    }
                }
            }
            else
            {
                result = E_SYNCHRO_RESULT_NOK;
            }

            P_SYNCHRO_Condition_Remove_Api_User(p);
        }
        else
        {
            result = E_SYNCHRO_RESULT_NOK;
        }
    }

    return result;
}

// Clear condition variable. If some thread are waiting for, these thread are notified.
// Warning, thread waiting for a signal try to relock mutex. If this mutex is never cleared or unlocked
// this function never returns !!!
eSynchroResult P_SYNCHRO_CONDITION_Clear(tCondVarHandle slotId)
{
    eSynchroResult result = E_SYNCHRO_RESULT_OK;

    if (slotId >= MAX_COND_VAR)
    {
        return E_SYNCHRO_RESULT_INVALID_PARAMETERS;
    }

    tCondVar* p = &gCondVarWks.tabWks[slotId];

    do
    {
        // Set quit flag
        P_SYNCHRO_Condition_Set_Quit_Flag(p);

        // Signal all thread waiting for this condition variable
        for (uint32_t i = 0; i < MAX_COND_VAR_WAITERS; i++)
        {
            {
                eSigStatus sigStatus = E_SIG_STATUS_NOT_RESERVED;
                __atomic_load(&p->tabSignals[i].sigStatus, &sigStatus, __ATOMIC_SEQ_CST);
                if (E_SIG_STATUS_WAIT_FOR_SIGNAL == sigStatus)
                {
                    k_sem_give(&p->tabSignals[i].signal);
                }
            }
        }

        // Try to go to de initializing state
        eSyncStatus expectedStatus = E_SYNC_STATUS_INITIALIZED | MASK_SET_QUIT_FLAG;
        eSyncStatus desiredStatus = E_SYNC_STATUS_DEINITIALIZING;
        bool bTransition = __atomic_compare_exchange(&p->status,        //
                                                     &expectedStatus,   //
                                                     &desiredStatus,    //
                                                     false,             //
                                                     __ATOMIC_SEQ_CST,  //
                                                     __ATOMIC_SEQ_CST); //

        // If deinitializing state reach, reset all signals, set result OK to stop retry loop
        // then mark new status as not initialized.
        if (bTransition)
        {
            for (uint32_t i = 0; i < MAX_COND_VAR_WAITERS; i++)
            {
                k_sem_reset(&p->tabSignals[i].signal);
            }

            result = E_SYNCHRO_RESULT_OK;

            desiredStatus = E_SYNC_STATUS_NOT_INITIALIZED;
            __atomic_store(&p->status, &desiredStatus, __ATOMIC_SEQ_CST);
        }
        // Others status indicates that operation is on going or API is in use.
        // Set result to invalid state, then yield.
        else if (E_SYNC_STATUS_DEINITIALIZING == (expectedStatus & ~MASK_SET_QUIT_FLAG) ||
                 E_SYNC_STATUS_INITIALIZED < (expectedStatus & ~MASK_SET_QUIT_FLAG) ||
                 E_SYNC_STATUS_INITIALIZING == (expectedStatus & ~MASK_SET_QUIT_FLAG))
        {
            result = E_SYNCHRO_RESULT_INVALID_STATE;
            k_yield();
        }
        // If state is not initialized, return NOK.
        else
        {
            result = E_SYNCHRO_RESULT_NOK;
        }
    } while (E_SYNCHRO_RESULT_INVALID_STATE == result);

    return result;
}

// *** Internal functions definitions for P_SYNCHRO_MUTEX API ***

static void P_SYNCHRO_MUTEX_CondVar_UnlockAndWait_Lock_Callback(void* pMutex)
{
    struct k_mutex* pk_mut = (struct k_mutex*) pMutex;
    k_mutex_lock(pk_mut, K_FOREVER);
}

static void P_SYNCHRO_MUTEX_CondVar_UnlockAndWait_UnLock_Callback(void* pMutex)
{
    struct k_mutex* pk_mut = (struct k_mutex*) pMutex;
    k_mutex_unlock(pk_mut);
}

// Initialize a mutex object
// Returns mutex handle to use with lock, unlock and clear.
// In case of failure, return UINT32_MAX invalid value.
tMutVarHandle P_SYNCHRO_MUTEX_Initialize(void)
{
    uint32_t slotId = UINT32_MAX;

    // Search for
    for (uint32_t i = 0; i < MAX_MUT_VAR; i++)
    {
        {
            eSyncStatus expectedStatus = E_SYNC_STATUS_NOT_INITIALIZED;
            eSyncStatus desiredStatus = E_SYNC_STATUS_INITIALIZING;
            bool bTransition = __atomic_compare_exchange(&gMutVarWks.tabWks[i].status, //
                                                         &expectedStatus,              //
                                                         &desiredStatus,               //
                                                         false,                        //
                                                         __ATOMIC_SEQ_CST,             //
                                                         __ATOMIC_SEQ_CST);            //
            if (bTransition)
            {
                gMutVarWks.tabWks[i].condVarHdl = P_SYNCHRO_CONDITION_Initialize();
                gMutVarWks.tabWks[i].lockCounter = 0;
                gMutVarWks.tabWks[i].ownerThread = NULL;
                k_mutex_init(&gMutVarWks.tabWks[i].lock);
                slotId = i;
                desiredStatus = E_SYNC_STATUS_INITIALIZED;
                __atomic_store(&gMutVarWks.tabWks[i].status, &desiredStatus, __ATOMIC_SEQ_CST);
                break;
            }
        }
    }

    return slotId;
}

// Clear a mutex object. All future calls to API will return NOK.
// If an API LOCK is in use, it will be immediatly unlocked.
// API LOCK returns in that case NOK.
eSynchroResult P_SYNCHRO_MUTEX_Clear(tMutVarHandle slotId)
{
    eSynchroResult result = E_SYNCHRO_RESULT_OK;
    if (slotId >= MAX_MUT_VAR)
    {
        return E_SYNCHRO_RESULT_NOK;
    }

    tMutVar* p = &gMutVarWks.tabWks[slotId];

    do
    {
        // Set quit flag
        P_SYNCHRO_Mutex_Set_Quit_Flag(p);

        // Signal all to unlock all P_SYNCHRO_MUTEX_Lock function
        P_SYNCHRO_CONDITION_SignalAll(p->condVarHdl);

        // Try to go to de initializing status
        eSyncStatus expectedStatus = E_SYNC_STATUS_INITIALIZED | MASK_SET_QUIT_FLAG;
        eSyncStatus desiredStatus = E_SYNC_STATUS_DEINITIALIZING;
        bool bTransition = __atomic_compare_exchange(&p->status,        //
                                                     &expectedStatus,   //
                                                     &desiredStatus,    //
                                                     false,             //
                                                     __ATOMIC_SEQ_CST,  //
                                                     __ATOMIC_SEQ_CST); //

        // If successful clear condition variable, else yield and retry
        if (bTransition)
        {
            P_SYNCHRO_CONDITION_Clear(p->condVarHdl); // Clear condition variable
            p->condVarHdl = UINT32_MAX;               // Handle set to invalid handle
            p->lockCounter = 0;                       // Reset lock counter
            p->ownerThread = NULL;                    // Reset owner thread
            desiredStatus = E_SYNC_STATUS_NOT_INITIALIZED;
            __atomic_store(&p->status, &desiredStatus, __ATOMIC_SEQ_CST);
            result = E_SYNCHRO_RESULT_OK; // Terminates loop
        }
        else if ((E_SYNC_STATUS_DEINITIALIZING == (expectedStatus & ~MASK_SET_QUIT_FLAG)) ||
                 (E_SYNC_STATUS_INITIALIZING == (expectedStatus & ~MASK_SET_QUIT_FLAG)) ||
                 ((expectedStatus & ~MASK_SET_QUIT_FLAG) > E_SYNC_STATUS_INITIALIZED))
        {
            result = E_SYNCHRO_RESULT_INVALID_STATE; // Invalid state, retry...
            k_yield();
        }
        else
        {
            result = E_SYNCHRO_RESULT_NOK; // Already cleared, nok, terminates loop
        }
    } while (E_SYNCHRO_RESULT_INVALID_STATE == result);

    return result;
}

// Lock a mutex object. Ok if successfully locked. Nok if cleared or invalid handle.
eSynchroResult P_SYNCHRO_MUTEX_Lock(tMutVarHandle slotId)
{
    eSynchroResult result = E_SYNCHRO_RESULT_OK;
    if (slotId >= MAX_MUT_VAR)
    {
        return E_SYNCHRO_RESULT_NOK;
    }

    tMutVar* p = &gMutVarWks.tabWks[slotId];

    eSyncStatus readStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    __atomic_load(&p->status, &readStatus, __ATOMIC_SEQ_CST);
    // Verify if quit operation on going.
    if ((readStatus & MASK_SET_QUIT_FLAG) != 0)
    {
        return E_SYNCHRO_RESULT_NOK;
    }

    // Check if well initialized
    eSyncStatus currentStatus = P_SYNCHRO_Mutex_Add_Api_User(p);

    if ((currentStatus & ~MASK_SET_QUIT_FLAG) > E_SYNC_STATUS_INITIALIZED)
    {
        // Start critical section
        k_mutex_lock(&p->lock, K_FOREVER);
        {
            // Check if lock counter incremented. If 0, else mutex can be locked.
            // Initialized new owner.
            if (0 == p->lockCounter)
            {
                p->ownerThread = k_current_get();
            }

            // If current owner is not current thread, mutex can't be locked.
            // Quit critical section and wait for unlock mutex complete operation
            if (p->ownerThread != k_current_get())
            {
                do
                {
                    result = P_SYNCHRO_CONDITION_UnlockAndWait(p->condVarHdl,                                         //
                                                               (void*) &p->lock,                                      //
                                                               P_SYNCHRO_MUTEX_CondVar_UnlockAndWait_Lock_Callback,   //
                                                               P_SYNCHRO_MUTEX_CondVar_UnlockAndWait_UnLock_Callback, //
                                                               UINT32_MAX);                                           //
                    // Reentering critical section. Verify if quit status has been mounted.
                    // If yes, return NOK.
                    if ((p->status & MASK_SET_QUIT_FLAG) != 0)
                    {
                        result = E_SYNCHRO_RESULT_NOK;
                    }
                    else
                    {
                        // If signal received and lock counter not incremented, so mutex can be locked.
                        // Raz lock counter and increment it.
                        if (E_SYNCHRO_RESULT_OK == result && 0 == p->lockCounter)
                        {
                            p->ownerThread = k_current_get();
                            p->lockCounter = 1;
                        }
                        else
                        {
                            // If lock counter already incremented, wait for new unlock operation...
                            if (E_SYNCHRO_RESULT_OK == result && p->lockCounter > 0)
                            {
                                result = E_SYNCHRO_RESULT_INVALID_STATE;
                            }
                            else
                            {
                                // If condition variable invalid, returns NOK
                                result = E_SYNCHRO_RESULT_NOK;
                            }
                        }
                    }

                } while (E_SYNCHRO_RESULT_INVALID_STATE == result);
            }
            else
            {
                // Current thread is the mutex owner, increment counter.
                p->lockCounter++;
            }
        }
        // End critical section
        k_mutex_unlock(&p->lock);

        P_SYNCHRO_Mutex_Remove_Api_User(&gMutVarWks.tabWks[slotId]);
    }
    else
    {
        result = E_SYNCHRO_RESULT_NOK;
    }
    return result;
}

// Unlock a mutex object
eSynchroResult P_SYNCHRO_MUTEX_Unlock(tMutVarHandle slotId) // Mutex handle
{
    if (slotId >= MAX_MUT_VAR)
    {
        return E_SYNCHRO_RESULT_NOK;
    }

    tMutVar* p = &gMutVarWks.tabWks[slotId];

    eSyncStatus readStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    __atomic_load(&p->status, &readStatus, __ATOMIC_SEQ_CST);
    // Verify if quit operation on going.
    if ((readStatus & MASK_SET_QUIT_FLAG) != 0)
    {
        return E_SYNCHRO_RESULT_NOK;
    }

    eSynchroResult result = E_SYNCHRO_RESULT_OK;

    eSyncStatus currentStatus = P_SYNCHRO_Mutex_Add_Api_User(p);

    // Check if mutex is well initialized.
    if ((currentStatus & ~MASK_SET_QUIT_FLAG) > E_SYNC_STATUS_INITIALIZED)
    {
        // Enter critical section
        k_mutex_lock(&p->lock, K_FOREVER);
        {
            // If current thread is the owner, unlock operation can be performed. Else returns NOK.
            if (p->ownerThread == k_current_get())
            {
                // Decrement lock counter.
                // If reaches 0, signal to all trying lock that mutex has been unlocked by owner thread.
                if (p->lockCounter > 0)
                {
                    p->lockCounter--;
                    if (0 == p->lockCounter)
                    {
                        p->ownerThread = NULL;
                        // Result of signal all indicates NO_WAITERS if no thread are trying to lock this mutex.
                        // Else, OK is returned.
                        result = P_SYNCHRO_CONDITION_SignalAll(p->condVarHdl);
                    }
                    else
                    {
                        // Waiters (even if exist) are ignored if lock counter is > 0
                        result = E_SYNCHRO_RESULT_NO_WAITERS;
                    }
                }
            }
            else
            {
                result = E_SYNCHRO_RESULT_NOK;
            }
        }
        k_mutex_unlock(&p->lock);
        P_SYNCHRO_Mutex_Remove_Api_User(&gMutVarWks.tabWks[slotId]);

        // This result indicates successful with waiters on this mutex. So, yield to avoid mutex starving
        // by a thread looping on this mutex.
        if (E_SYNCHRO_RESULT_OK == result)
        {
            k_yield();
        }
    }
    else
    {
        result = E_SYNCHRO_RESULT_NOK;
    }

    return result;
}

// Set quit flag and returns new status with quit flag
static inline eSyncStatus P_SYNCHRO_Condition_Set_Quit_Flag(tCondVar* p)
{
    eSyncStatus currentStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    eSyncStatus newStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    bool bTransition = false;
    do
    {
        __atomic_load(&p->status, &currentStatus, __ATOMIC_SEQ_CST);
        newStatus = currentStatus | 0x80000000;

        bTransition = __atomic_compare_exchange(&p->status,        //
                                                &currentStatus,    //
                                                &newStatus,        //
                                                false,             //
                                                __ATOMIC_SEQ_CST,  //
                                                __ATOMIC_SEQ_CST); //

    } while (!bTransition);
    return newStatus;
}

// Returns new status with quit flag
static inline eSyncStatus P_SYNCHRO_Condition_Add_Api_User(tCondVar* p)
{
    eSyncStatus currentStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    eSyncStatus newStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    bool bTransition = false;
    do
    {
        __atomic_load(&p->status, &currentStatus, __ATOMIC_SEQ_CST);
        if ((currentStatus & ~MASK_SET_QUIT_FLAG) >= E_SYNC_STATUS_INITIALIZED)
        {
            newStatus = currentStatus + 1;
        }
        else
        {
            newStatus = currentStatus;
        }
        bTransition = __atomic_compare_exchange(&p->status,        //
                                                &currentStatus,    //
                                                &newStatus,        //
                                                false,             //
                                                __ATOMIC_SEQ_CST,  //
                                                __ATOMIC_SEQ_CST); //

    } while (!bTransition);
    return newStatus;
}

// Returns new status with quit flag
static inline eSyncStatus P_SYNCHRO_Condition_Remove_Api_User(tCondVar* p)
{
    eSyncStatus currentStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    eSyncStatus newStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    bool bTransition = false;
    do
    {
        __atomic_load(&p->status, &currentStatus, __ATOMIC_SEQ_CST);
        if ((currentStatus & ~MASK_SET_QUIT_FLAG) > E_SYNC_STATUS_INITIALIZED)
        {
            newStatus = currentStatus - 1;
        }
        else
        {
            newStatus = currentStatus;
        }
        bTransition = __atomic_compare_exchange(&p->status,        //
                                                &currentStatus,    //
                                                &newStatus,        //
                                                false,             //
                                                __ATOMIC_SEQ_CST,  //
                                                __ATOMIC_SEQ_CST); //

    } while (!bTransition);

    return newStatus;
}

// Set quit flag and returns new status with quit flag
static inline eSyncStatus P_SYNCHRO_Mutex_Set_Quit_Flag(tMutVar* p)
{
    eSyncStatus currentStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    eSyncStatus newStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    bool bTransition = false;
    do
    {
        __atomic_load(&p->status, &currentStatus, __ATOMIC_SEQ_CST);
        newStatus = currentStatus | 0x80000000;

        bTransition = __atomic_compare_exchange(&p->status,        //
                                                &currentStatus,    //
                                                &newStatus,        //
                                                false,             //
                                                __ATOMIC_SEQ_CST,  //
                                                __ATOMIC_SEQ_CST); //

    } while (!bTransition);
    return newStatus;
}

// Returns new status with quit flag
static inline eSyncStatus P_SYNCHRO_Mutex_Add_Api_User(tMutVar* p)
{
    eSyncStatus currentStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    eSyncStatus newStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    bool bTransition = false;
    do
    {
        __atomic_load(&p->status, &currentStatus, __ATOMIC_SEQ_CST);
        if ((currentStatus & ~MASK_SET_QUIT_FLAG) >= E_SYNC_STATUS_INITIALIZED)
        {
            newStatus = currentStatus + 1;
        }
        else
        {
            newStatus = currentStatus;
        }
        bTransition = __atomic_compare_exchange(&p->status,        //
                                                &currentStatus,    //
                                                &newStatus,        //
                                                false,             //
                                                __ATOMIC_SEQ_CST,  //
                                                __ATOMIC_SEQ_CST); //

    } while (!bTransition);
    return newStatus;
}

// Returns new status with quit flag
static inline eSyncStatus P_SYNCHRO_Mutex_Remove_Api_User(tMutVar* p)
{
    eSyncStatus currentStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    eSyncStatus newStatus = E_SYNC_STATUS_NOT_INITIALIZED;
    bool bTransition = false;
    do
    {
        __atomic_load(&p->status, &currentStatus, __ATOMIC_SEQ_CST);
        if ((currentStatus & ~MASK_SET_QUIT_FLAG) > E_SYNC_STATUS_INITIALIZED)
        {
            newStatus = currentStatus - 1;
        }
        else
        {
            newStatus = currentStatus;
        }
        bTransition = __atomic_compare_exchange(&p->status,        //
                                                &currentStatus,    //
                                                &newStatus,        //
                                                false,             //
                                                __ATOMIC_SEQ_CST,  //
                                                __ATOMIC_SEQ_CST); //

    } while (!bTransition);

    return newStatus;
}

// *** Public SOPC synchro api ***

// Initialize condition variable
SOPC_ReturnStatus Condition_Init(Condition* cond)
{
    if (NULL == cond)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    SOPC_ReturnStatus result = SOPC_STATUS_OK;
    tCondVarHandle handle = P_SYNCHRO_CONDITION_Initialize();
    *cond = handle;

    if (UINT32_MAX == handle)
    {
        result = SOPC_STATUS_NOK;
    }

    return result;
}

// Clear condition variable
SOPC_ReturnStatus Condition_Clear(Condition* cond)
{
    if (NULL == cond)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    SOPC_ReturnStatus resSOPC = SOPC_STATUS_OK;
    eSynchroResult resSync = E_SYNCHRO_RESULT_OK;

    tCondVarHandle handle = *cond;

    resSync = P_SYNCHRO_CONDITION_Clear(handle);

    if (E_SYNCHRO_RESULT_OK == resSync)
    {
        resSOPC = SOPC_STATUS_OK;
    }
    else
    {
        resSOPC = SOPC_STATUS_NOK;
    }

    return resSOPC;
}

// Must be called between lock and unlock of Mutex used to wait on condition
SOPC_ReturnStatus Condition_SignalAll(Condition* cond)
{
    if (NULL == cond)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    SOPC_ReturnStatus resSOPC = SOPC_STATUS_OK;
    eSynchroResult resSync = E_SYNCHRO_RESULT_OK;

    tCondVarHandle handle = *cond;

    resSync = P_SYNCHRO_CONDITION_SignalAll(handle);

    if (E_SYNCHRO_RESULT_OK == resSync)
    {
        resSOPC = SOPC_STATUS_OK;
    }
    else if (E_SYNCHRO_RESULT_NO_WAITERS == resSync)
    {
        resSOPC = SOPC_STATUS_INVALID_STATE;
    }
    else
    {
        resSOPC = SOPC_STATUS_NOK;
    }

    return resSOPC;
}

// Initialize mutex
SOPC_ReturnStatus Mutex_Initialization(Mutex* mut)
{
    if (NULL == mut)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    SOPC_ReturnStatus resSOPC = SOPC_STATUS_OK;

    tMutVarHandle handle = P_SYNCHRO_MUTEX_Initialize();
    *mut = handle;
    if (UINT32_MAX == handle)
    {
        resSOPC = SOPC_STATUS_NOK;
    }

    return resSOPC;
}

// Clear mutex
SOPC_ReturnStatus Mutex_Clear(Mutex* mut)
{
    if (NULL == mut)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }
    SOPC_ReturnStatus resSOPC = SOPC_STATUS_OK;
    eSynchroResult resSync = E_SYNCHRO_RESULT_OK;

    tMutVarHandle handle = *mut;

    resSync = P_SYNCHRO_MUTEX_Clear(handle);

    if (E_SYNCHRO_RESULT_OK == resSync)
    {
        resSOPC = SOPC_STATUS_OK;
    }
    else
    {
        resSOPC = SOPC_STATUS_NOK;
    }

    return resSOPC;
}

// Lock mutex
SOPC_ReturnStatus Mutex_Lock(Mutex* mut)
{
    if (NULL == mut)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }
    SOPC_ReturnStatus resSOPC = SOPC_STATUS_OK;
    eSynchroResult resSync = E_SYNCHRO_RESULT_OK;

    tMutVarHandle handle = *mut;

    resSync = P_SYNCHRO_MUTEX_Lock(handle);

    if (E_SYNCHRO_RESULT_OK == resSync)
    {
        resSOPC = SOPC_STATUS_OK;
    }
    else
    {
        resSOPC = SOPC_STATUS_NOK;
    }

    return resSOPC;
}

// Unlock mutex
SOPC_ReturnStatus Mutex_Unlock(Mutex* mut)
{
    if (NULL == mut)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }
    SOPC_ReturnStatus resSOPC = SOPC_STATUS_OK;
    eSynchroResult resSync = E_SYNCHRO_RESULT_OK;

    tMutVarHandle handle = *mut;

    resSync = P_SYNCHRO_MUTEX_Unlock(handle);

    if (E_SYNCHRO_RESULT_OK == resSync || E_SYNCHRO_RESULT_NO_WAITERS == resSync)
    {
        resSOPC = SOPC_STATUS_OK;
    }
    else
    {
        resSOPC = SOPC_STATUS_NOK;
    }

    return resSOPC;
}

// Callback which defines lock and unlock implementation
static void Mutex_UnlockAndTimedWaitCond_LockCallback(void* pMutex)
{
    tMutVarHandle* pHandle = (tMutVarHandle*) pMutex;
    if (pHandle != NULL)
    {
        P_SYNCHRO_MUTEX_Lock(*pHandle);
    }

    return;
}

static void Mutex_UnlockAndTimedWaitCond_UnLockCallback(void* pMutex)
{
    tMutVarHandle* pHandle = (tMutVarHandle*) pMutex;
    if (pHandle != NULL)
    {
        P_SYNCHRO_MUTEX_Unlock(*pHandle);
    }
    return;
}

// Lock on return. Return SOPC_STATUS_TIMEOUT in case of timeout before condition signaled
SOPC_ReturnStatus Mutex_UnlockAndTimedWaitCond(Condition* cond, Mutex* mut, uint32_t milliSecs)
{
    if (NULL == cond || NULL == mut)
    {
        return SOPC_STATUS_INVALID_PARAMETERS;
    }

    SOPC_ReturnStatus resSOPC = SOPC_STATUS_OK;
    eSynchroResult resSync = E_SYNCHRO_RESULT_OK;

    tMutVarHandle handleMut = *mut;
    tCondVarHandle handleCond = *cond;

    resSync = P_SYNCHRO_CONDITION_UnlockAndWait(handleCond,                                  //
                                                &handleMut,                                  //
                                                Mutex_UnlockAndTimedWaitCond_LockCallback,   //
                                                Mutex_UnlockAndTimedWaitCond_UnLockCallback, //
                                                milliSecs);                                  //

    switch (resSync)
    {
    case E_SYNCHRO_RESULT_OK:
        resSOPC = SOPC_STATUS_OK;
        break;
    case E_SYNCHRO_RESULT_TMO:
        resSOPC = SOPC_STATUS_TIMEOUT;
        break;
    default:
        resSOPC = SOPC_STATUS_NOK;
        break;
    }

    return resSOPC;
}

// Lock on return
SOPC_ReturnStatus Mutex_UnlockAndWaitCond(Condition* cond, Mutex* mut)
{
    return Mutex_UnlockAndTimedWaitCond(cond, mut, UINT32_MAX);
}