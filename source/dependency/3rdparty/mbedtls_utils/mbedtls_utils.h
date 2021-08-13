/*
 *  Copyright (C) 2006-2015, ARM Limited, All Rights Reserved
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Licensed under the Apache License, Version 2.0 (the "License"); you may
 *  not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  This file is part of mbed TLS (https://tls.mbed.org)
 */

/**
 * @file mbedtls_utils.h
 * @brief Helper functions originating from mbedTLS.
 */

/* Standard includes. */
#include <string.h>

/*-----------------------------------------------------------*/

/**
 * @brief Converts PEM documents into DER formatted byte arrays.
 * This is a helper function from MbedTLS util pem2der.c
 * (https://github.com/ARMmbed/mbedtls/blob/development/programs/util/pem2der.c#L75)
 *
 * @param pucInput[in]    Pointer to PEM object
 * @param xLen[in]        Length of PEM object
 * @param pucOutput[out]  Pointer to buffer where DER oboject will be placed
 * @param pxOlen[in/out]  Pointer to length of DER buffer.  This value is updated
 *                        to contain the actual length of the converted DER object.
 *
 * @return 0 if successful. Negative if conversion failed. If buffer is not
 * large enough to hold converted object, pxOlen is still updated but -1 is
 * returned.
 */
int convert_pem_to_der( const unsigned char * pucInput,
                        size_t xLen,
                        unsigned char * pucOutput,
                        size_t * pxOlen );

/*-----------------------------------------------------------*/



/**
 * @brief This function is a modified version of the static function
 * rsa_rsassa_pkcs1_v15_encode() inside of rsa.c in MbedTLS.  It has been
 * extracted so that corePKCS11 libraries and testing may use it.
 *
 * Formats cryptographically hashed data for RSA signing in accordance
 * with PKCS #1 version 1.5.
 *
 * Currently assumes SHA-256.
 *
 * @param hash[in]     Buffer containing the hashed message or the raw data.
 * @param dst_len[in]  Length of the encoded message.
 * @param dst[out]     Buffer to hold the encoded message.
 */
int PKI_RSA_RSASSA_PKCS1_v15_Encode( const unsigned char * hash,
                                     size_t dst_len,
                                     unsigned char * dst );
