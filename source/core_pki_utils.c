/*
 * corePKCS11
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 * @file core_pki_utils.c
 * @brief Helper functions for PKCS #11
 */
#include "core_pki_utils.h"

/* CRT includes. */
#include <stdint.h>
#include <string.h>

/**
 * @ingroup pkcs11_macros
 * @brief Failure value for PKI utils functions.
 */
#define FAILURE    ( -1 )

/*-----------------------------------------------------------*/

/* Convert the EC signature from DER encoded to PKCS #11 format. */
/* @[declare pkcs11_utils_pkipkcs11signaturetombedtlssignature] */
int8_t PKI_mbedTLSSignatureToPkcs11Signature( uint8_t * pxSignaturePKCS,
                                              size_t xSignaturePKCSLen,
                                              const uint8_t * pxMbedSignature,
                                              size_t xMbedSignatureLen )
{
    int8_t xReturn = 0;
    size_t xOffset = 0;
    size_t xComponentLen;
    size_t xDataOffset;

    if( ( pxSignaturePKCS == NULL ) || ( pxMbedSignature == NULL ) ||
        ( xMbedSignatureLen == 0 ) )
    {
        xReturn = FAILURE;
    }

    /* Need at least 64 bytes in the output buffer for the PKCS #11 signature. */
    if( ( xReturn == 0 ) && ( xSignaturePKCSLen < 64U ) )
    {
        xReturn = FAILURE;
    }

    if( xReturn == 0 )
    {
        /* The signature has the format
         * SEQUENCE LENGTH (of entire rest of signature)
         *      INTEGER LENGTH  (of R component)
         *      INTEGER LENGTH  (of S component)
         */

        /* Validate SEQUENCE tag (0x30) and that we have at least the
         * SEQUENCE tag, length, INTEGER tag, length, and R/S bytes. */
        if( ( xMbedSignatureLen < 68U ) ||
            ( pxMbedSignature[ 0 ] != 0x30U ) )
        {
            xReturn = FAILURE;
        }
    }

    /* The new signature will be 64 bytes long (32 bytes for R, 32 bytes for S).
     * Zero this buffer out in case a component is shorter than 32 bytes. */
    if( xReturn == 0 )
    {
        ( void ) memset( pxSignaturePKCS, 0, 64 );
    }

    if( xReturn == 0 )
    {
        /* Skip SEQUENCE tag and length to reach the R INTEGER. */
        xOffset = 2;

        /********* R Component. *********/

        /* Validate INTEGER tag for R. */
        if( pxMbedSignature[ xOffset ] != 0x02U )
        {
            xReturn = FAILURE;
        }

        /* And get the R Componenent length. */
        xOffset++;
        xComponentLen = ( size_t ) pxMbedSignature[ xOffset ];
    }

    if( xReturn == 0 )
    {
        /* Now read the R Component value. */
        xOffset++;
        xDataOffset = xOffset;

        /* Strip leading zero padding (DER sign byte). */
        if( ( xComponentLen > 0U ) &&
            ( xDataOffset < xMbedSignatureLen ) &&
            ( pxMbedSignature[ xDataOffset ] == 0x00U ) )
        {
            xDataOffset++;
            xComponentLen--;
        }

        /* Validate R component: non-zero, fits in 32 bytes, and within buffer. */
        if( ( xComponentLen == 0U ) ||
            ( xComponentLen > 32U ) ||
            ( ( xDataOffset + xComponentLen ) > xMbedSignatureLen ) )
        {
            xReturn = FAILURE;
        }
    }

    if( xReturn == 0 )
    {
        ( void ) memcpy( &( pxSignaturePKCS[ 32U - xComponentLen ] ),
                         &( pxMbedSignature[ xDataOffset ] ),
                         xComponentLen );

        /* Advance past the full R component (including any leading zero). */
        xOffset += ( size_t ) pxMbedSignature[ xOffset - 1U ];

        /********** S Component. ***********/

        /* Validate INTEGER tag for S. */
        if( ( xOffset >= xMbedSignatureLen ) ||
            ( pxMbedSignature[ xOffset ] != 0x02U ) )
        {
            xReturn = FAILURE;
        }
    }

    if( xReturn == 0 )
    {
        xOffset++;

        /* Read S component length. */
        if( xOffset >= xMbedSignatureLen )
        {
            xReturn = FAILURE;
        }
    }

    if( xReturn == 0 )
    {
        xComponentLen = ( size_t ) pxMbedSignature[ xOffset ];
        xOffset++;
        xDataOffset = xOffset;

        /* Strip leading zero padding (DER sign byte). */
        if( ( xComponentLen > 0U ) &&
            ( xDataOffset < xMbedSignatureLen ) &&
            ( pxMbedSignature[ xDataOffset ] == 0x00U ) )
        {
            xDataOffset++;
            xComponentLen--;
        }

        /* Validate S component: non-zero, fits in 32 bytes, and within buffer. */
        if( ( xComponentLen == 0U ) ||
            ( xComponentLen > 32U ) ||
            ( ( xDataOffset + xComponentLen ) > xMbedSignatureLen ) )
        {
            xReturn = FAILURE;
        }
    }

    if( xReturn == 0 )
    {
        ( void ) memcpy( &( pxSignaturePKCS[ 64U - xComponentLen ] ),
                         &( pxMbedSignature[ xDataOffset ] ),
                         xComponentLen );
    }

    return xReturn;
}
/* @[declare pkcs11_utils_pkipkcs11signaturetombedtlssignature] */
/*-----------------------------------------------------------*/


/* Convert an EC signature from PKCS #11 format to DER encoded. */
/* @[declare pkcs11_utils_pkimbedtlssignaturetopkcs11signature] */
int8_t PKI_pkcs11SignatureTombedTLSSignature( uint8_t * pucSig,
                                              size_t xSigBufLen,
                                              size_t * pxSigLen )
{
    int8_t xReturn = 0;
    uint8_t ucTemp[ 64 ] = { 0 };
    size_t xOutLen;
    size_t xOffset;
    uint8_t ucRPad;
    uint8_t ucSPad;

    if( ( pucSig == NULL ) || ( pxSigLen == NULL ) )
    {
        xReturn = FAILURE;
    }

    /* Need at least 64 bytes to read the PKCS #11 input,
     * 72 bytes for largest ECDSA output. */
    if( ( xReturn == 0 ) && ( xSigBufLen < 72U ) )
    {
        xReturn = FAILURE;
    }

    if( xReturn == 0 )
    {
        ( void ) memcpy( ucTemp, pucSig, 64 );

        /* Determine if R and S need a leading 0x00 pad to avoid being
         * interpreted as negative in ASN.1. */
        ucRPad = ( ( ucTemp[ 0 ] & 0x80U ) != 0U ) ? 1U : 0U;
        ucSPad = ( ( ucTemp[ 32 ] & 0x80U ) != 0U ) ? 1U : 0U;

        /* Total DER output: SEQUENCE(1) + LENGTH(1) +
         *   R component INTEGER(1) + LENGTH(1) + pad + 32 +
         *   S component INTEGER(1) + LENGTH(1) + pad + 32 */
        xOutLen = 2U + 2U + ucRPad + 32U + 2U + ucSPad + 32U;

        xOffset = 0;

        /* SEQUENCE tag and length. */
        pucSig[ xOffset++ ] = 0x30;
        pucSig[ xOffset++ ] = ( uint8_t ) ( xOutLen - 2U );

        /* R INTEGER. */
        pucSig[ xOffset++ ] = 0x02;
        pucSig[ xOffset++ ] = ( uint8_t ) ( 32U + ucRPad );

        if( ucRPad != 0U )
        {
            pucSig[ xOffset++ ] = 0x00;
        }

        ( void ) memcpy( &( pucSig[ xOffset ] ), ucTemp, 32 );
        xOffset += 32U;

        /* S INTEGER. */
        pucSig[ xOffset++ ] = 0x02;
        pucSig[ xOffset++ ] = ( uint8_t ) ( 32U + ucSPad );

        if( ucSPad != 0U )
        {
            pucSig[ xOffset++ ] = 0x00;
        }

        ( void ) memcpy( &( pucSig[ xOffset ] ), &( ucTemp[ 32 ] ), 32 );

        *pxSigLen = xOutLen;
    }

    return xReturn;
}
/* @[declare pkcs11_utils_pkimbedtlssignaturetopkcs11signature] */
