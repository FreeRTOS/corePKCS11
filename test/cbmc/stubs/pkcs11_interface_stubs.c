/*
 * corePKCS v2.0.0
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
 */

/**
 * @file pkcs11_interface_stubs.c
 * @brief Stubs to mock calls to PKCS #11.
 */

#include <stddef.h>

#include "core_pkcs11.h"
#include "pkcs11.h"

CK_DECLARE_FUNCTION( CK_RV, C_Initialize )( CK_VOID_PTR pInitArgs )
{
    return CKR_OK;
}

CK_DECLARE_FUNCTION( CK_RV, C_Login )( CK_VOID_PTR pInitArgs )
{
    return CKR_OK;
}

CK_DECLARE_FUNCTION( CK_RV, C_OpenSession )( CK_VOID_PTR pInitArgs )
{
    return CKR_OK;
}

CK_DECLARE_FUNCTION( CK_RV, C_FindObjectsInit )( CK_SESSION_HANDLE hSession,
                                                 CK_ATTRIBUTE_PTR pTemplate,
                                                 CK_ULONG ulCount )
{
    return CKR_OK;
}

CK_DECLARE_FUNCTION( CK_RV, C_FindObjects )( CK_SESSION_HANDLE hSession,
                                             CK_OBJECT_HANDLE_PTR phObject,
                                             CK_ULONG ulMaxObjectCount,
                                             CK_ULONG_PTR pulObjectCount )
{
    return CKR_OK;
}

CK_DECLARE_FUNCTION( CK_RV, C_FindObjectsFinal )( CK_SESSION_HANDLE hSession )
{
    return CKR_OK;
}

CK_DECLARE_FUNCTION( CK_RV, C_GetSlotList )( CK_BBOOL tokenPresent,
                                             CK_SLOT_ID_PTR pSlotList,
                                             CK_ULONG_PTR pulCount )
{
    int32_t ulCount = nondet_int32();

    /* Most slot lists are less than 10, as it represents an individual HSM. corePKCS11 only
     * has 1 slot (This is allowed and many implementations do this. */
    __CPROVER_assume( ( ulCount > 0 ) );
    __CPROVER_assert( pulCount != NULL, "The count pointer can never be NULL." );

    CK_SLOT_ID * pxSlot = malloc( ulCount );
    __CPROVER_assume( pxSlot != NULL );

    if( pSlotList != NULL )
    {
        *pSlotList = pxSlot;
    }

    *pulCount = ulCount;

    return CKR_OK;
}

CK_DECLARE_FUNCTION( CK_RV, C_GetFunctionList )( CK_FUNCTION_LIST_PTR_PTR ppFunctionList )
{
    static CK_FUNCTION_LIST prvP11FunctionList =
    {
        { CRYPTOKI_VERSION_MAJOR, CRYPTOKI_VERSION_MINOR },
        C_Initialize,
        NULL,
        NULL, /*C_GetInfo */
        C_GetFunctionList,
        C_GetSlotList,
        NULL, /*C_GetSlotInfo*/
        NULL,
        NULL, /*C_GetMechanismList*/
        NULL,
        NULL,
        NULL, /*C_InitPIN*/
        NULL, /*C_SetPIN*/
        C_OpenSession,
        NULL,
        NULL, /*C_CloseAllSessions*/
        NULL, /*C_GetSessionInfo*/
        NULL, /*C_GetOperationState*/
        NULL, /*C_SetOperationState*/
        C_Login,
        NULL, /*C_Logout*/
        C_CreateObject,
        NULL, /*C_CopyObject*/
        C_DestroyObject,
        NULL, /*C_GetObjectSize*/
        C_GetAttributeValue,
        NULL, /*C_SetAttributeValue*/
        C_FindObjectsInit,
        C_FindObjects,
        C_FindObjectsFinal,
        NULL, /*C_EncryptInit*/
        NULL, /*C_Encrypt*/
        NULL, /*C_EncryptUpdate*/
        NULL, /*C_EncryptFinal*/
        NULL, /*C_DecryptInit*/
        NULL, /*C_Decrypt*/
        NULL, /*C_DecryptUpdate*/
        NULL, /*C_DecryptFinal*/
        C_DigestInit,
        NULL, /*C_Digest*/
        C_DigestUpdate,
        NULL, /* C_DigestKey*/
        C_DigestFinal,
        C_SignInit,
        C_Sign,
        NULL, /*C_SignUpdate*/
        NULL, /*C_SignFinal*/
        NULL, /*C_SignRecoverInit*/
        NULL, /*C_SignRecover*/
        C_VerifyInit,
        C_Verify,
        NULL, /*C_VerifyUpdate*/
        NULL, /*C_VerifyFinal*/
        NULL, /*C_VerifyRecoverInit*/
        NULL, /*C_VerifyRecover*/
        NULL, /*C_DigestEncryptUpdate*/
        NULL, /*C_DecryptDigestUpdate*/
        NULL, /*C_SignEncryptUpdate*/
        NULL, /*C_DecryptVerifyUpdate*/
        NULL, /*C_GenerateKey*/
        C_GenerateKeyPair,
        NULL, /*C_WrapKey*/
        NULL, /*C_UnwrapKey*/
        NULL, /*C_DeriveKey*/
        NULL, /*C_SeedRandom*/
        C_GenerateRandom,
        NULL, /*C_GetFunctionStatus*/
        NULL, /*C_CancelFunction*/
        NULL  /*C_WaitForSlotEvent*/
    };

    if( nondet_bool() )
    {
        if( nondet_bool() )
        {
            *ppFunctionList = NULL;
        }
        else
        {
            prvP11FunctionList.C_GetSlotList = NULL;
            *ppFunctionList = &prvP11FunctionList;
        }
    }
    else
    {
        *ppFunctionList = &prvP11FunctionList;
    }

    return CKR_OK;
}
