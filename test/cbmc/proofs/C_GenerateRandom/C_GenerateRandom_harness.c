/*
 * corePKCS11 v3.0.2
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
 * @file C_GenerateRandom_harness.c
 * @brief Implements the proof harness for C_GenerateRandom function.
 */

#include <stddef.h>
#include <stdlib.h>
#include "mbedtls/sha256.h"
#include "mbedtls/cmac.h"
#include "mbedtls/pk.h"
#include "core_pkcs11.h"

/* Internal struct for corePKCS11 mbed TLS implementation, but we don't really care what it contains
 * in this proof.
 *
 * It is just copied over from "core_pkcs11_mbedtls.c" so the structure is correct.
 */
typedef struct P11Session
{
    CK_ULONG ulState;
    CK_BBOOL xOpened;
    CK_MECHANISM_TYPE xOperationDigestMechanism;
    CK_BYTE * pxFindObjectLabel;
    CK_ULONG xFindObjectLabelLen;
    CK_MECHANISM_TYPE xOperationVerifyMechanism;
    mbedtls_threading_mutex_t xVerifyMutex;
    CK_OBJECT_HANDLE xVerifyKeyHandle;
    mbedtls_pk_context xVerifyKey;
    CK_MECHANISM_TYPE xOperationSignMechanism;
    mbedtls_threading_mutex_t xSignMutex;
    CK_OBJECT_HANDLE xSignKeyHandle;
    mbedtls_pk_context xSignKey;
    mbedtls_sha256_context xSHA256Context;
    CK_OBJECT_HANDLE xHMACKeyHandle;
    mbedtls_md_context_t xHMACSecretContext;
    CK_OBJECT_HANDLE xCMACKeyHandle;
    mbedtls_cipher_context_t xCMACSecretContext;
} P11Session_t;

CK_RV __CPROVER_file_local_core_pkcs11_mbedtls_c_prvCheckValidSessionAndModule( const P11Session_t * pxSession )
{
    CK_RV xResult;

    return xResult;
}

void harness()
{
    CK_BYTE_PTR pucRandData;
    CK_ULONG ulRandLen;
    CK_SESSION_HANDLE xSession;

    pucRandData = malloc( ( sizeof( CK_BYTE ) ) * ulRandLen );
    ( void ) C_GenerateRandom( xSession, pucRandData, ulRandLen );
}
