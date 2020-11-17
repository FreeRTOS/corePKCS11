/*
 * corePKCS11 V2.0.0
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
 * @file C_Sign_harness.c
 * @brief Implements the proof harness for C_Sign function.
 */

#include <stddef.h>
#include "core_pkcs11.h"

void harness()
{

    CK_RV xResult;
    CK_FLAGS xFlags;
    CK_MECHANISM xMechanism;
    CK_OBJECT_HANDLE hKey;
    CK_ULONG ulDataLen;
    CK_ULONG ulSignatureLen;

    CK_SESSION_HANDLE xSession;
    __CPROVER_assume( ulDataLen == pkcs11SHA256_DIGEST_LENGTH );

    CK_BYTE_PTR pData = malloc( sizeof( CK_BYTE ) * ulDataLen );
     CK_BYTE_PTR pSignature = malloc( sizeof( CK_BYTE ) * pkcs11ECDSA_P256_SIGNATURE_LENGTH );

    xResult = C_Initialize( NULL );
    __CPROVER_assert( xResult == CKR_OK, "PKCS #11 module needs to be initialized"
                                         " to be uninitialized." );

    xResult = C_OpenSession( 0, xFlags, NULL, 0, &xSession );

    C_Create

    if( xResult == CKR_OK )
    {
      xResult =  C_SignInit( xSession, &xMechanism, hKey );
    }
    
    if( xResult == CKR_OK )
    {
      xResult = C_Sign( xSession, pData, ulDataLen, NULL, &ulSignatureLen );
    }

    if( xResult == CKR_OK )
    {
      ( void ) C_Sign( xSession, pData, ulDataLen, pSignature, &ulSignatureLen );
    }
}
