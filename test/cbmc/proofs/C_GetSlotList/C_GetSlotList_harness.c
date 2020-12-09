/*
 * corePKCS11 V3.0.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file C_GetSlotList_harness.c
 * @brief Implements the proof harness for C_GetSlotList function.
 */

#include <stddef.h>
#include "core_pkcs11.h"

void harness()
{
    CK_BBOOL xToken;
    CK_ULONG ulSlotSize;
    CK_RV xResult;

    /* Respect the API contract. PKCS #11 MUST be initialized before getting a slot. */
    xResult = C_Initialize( NULL );
    __CPROVER_assume( xResult == CKR_OK );

    /* At the time of writing this proof corePKCS11 only has one slot.
     * Should this change please change the below assumption to new
     * number of slots.
     */
    __CPROVER_assume( ulSlotSize <= 1 );
    CK_SLOT_ID_PTR pxSlot = nondet_bool() ? malloc( sizeof( CK_SLOT_ID ) * ulSlotSize ) : NULL;

    ( void ) C_GetSlotList( xToken, pxSlot, &ulSlotSize );
    ( void ) C_GetSlotList( xToken, pxSlot, NULL );
}
