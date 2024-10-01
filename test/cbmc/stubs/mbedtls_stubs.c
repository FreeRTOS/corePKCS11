/*
 * corePKCS11 v3.6.1
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
 * @file mbedtls_stubs.c
 * @brief Stubs for mbed TLS functions.
 */

#include "mbedtls/pk.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/threading.h"
#include "mbedtls/bignum.h"
#include "mbedtls/cipher.h"
#include "mbedtls/cmac.h"
#include "mbedtls/ecp.h"
#include "mbedtls/md.h"
#include "mbedtls/sha256.h"
#include "mbedtls/x509_crt.h"


void mbedtls_entropy_init( mbedtls_entropy_context * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

void mbedtls_entropy_free( mbedtls_entropy_context * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

void mbedtls_ctr_drbg_init( mbedtls_ctr_drbg_context * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

int mbedtls_ctr_drbg_seed( mbedtls_ctr_drbg_context * ctx,
                           int ( * f_entropy )( void *, unsigned char *, size_t ),
                           void * p_entropy,
                           const unsigned char * custom,
                           size_t len )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( f_entropy != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( p_entropy != NULL, "Received an unexpected NULL pointer." );
    return nondet_bool() ? 0 : -1;
}

int mbedtls_ctr_drbg_random( void * p_rng,
                             unsigned char * output,
                             size_t output_len )
{
    __CPROVER_assert( p_rng != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( output != NULL, "Received an unexpected NULL pointer." );
    return nondet_bool() ? 0 : -1;
}

void mbedtls_ctr_drbg_free( mbedtls_ctr_drbg_context * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

int mbedtls_pk_sign( mbedtls_pk_context * ctx,
                     mbedtls_md_type_t md_alg,
                     const unsigned char * hash,
                     size_t hash_len,
                     unsigned char * sig,
                     size_t * sig_len,
                     int ( * f_rng )( void *, unsigned char *, size_t ),
                     void * p_rng )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( hash != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( sig != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( sig_len != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( f_rng != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( p_rng != NULL, "Received an unexpected NULL pointer." );
    return nondet_bool() ? 0 : -1;
}

int mbedtls_ecdsa_verify( mbedtls_ecp_group * grp,
                          const unsigned char * buf,
                          size_t blen,
                          const mbedtls_ecp_point * Q,
                          const mbedtls_mpi * r,
                          const mbedtls_mpi * s )
{
    __CPROVER_assert( grp != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( buf != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( Q != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( r != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( s != NULL, "Received an unexpected NULL pointer." );

    return nondet_bool() ? 0 : -1;
}

void mbedtls_sha256_init( mbedtls_sha256_context * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    return nondet_bool() ? 0 : -1;
}

int mbedtls_sha256_starts_ret( mbedtls_sha256_context * ctx,
                               int is224 )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( is224 == 0, "We are only doing sha256 currently." );
    return nondet_bool() ? 0 : -1;
}

int mbedtls_sha256_finish_ret( mbedtls_sha256_context * ctx,
                               unsigned char output[ 32 ] )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( output != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( __CPROVER_OBJECT_SIZE( output ) == 32UL, "SHA256 output buffers must be 32 bytes." );

    return 32;
}

int mbedtls_pk_verify( mbedtls_pk_context * ctx,
                       mbedtls_md_type_t md_alg,
                       const unsigned char * hash,
                       size_t hash_len,
                       const unsigned char * sig,
                       size_t sig_len )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( hash != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( sig != NULL, "Received an unexpected NULL pointer." );
    return nondet_bool() ? 0 : -1;
}



static void threading_mutex_init( mbedtls_threading_mutex_t * mutex )
{
    mbedtls_threading_mutex_t * m = malloc( sizeof( mbedtls_threading_mutex_t ) );

    __CPROVER_assert( mutex != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assume( m != NULL );
    mutex = m;
}

static void threading_mutex_free( mbedtls_threading_mutex_t * mutex )
{
    __CPROVER_assert( mutex != NULL, "Received an unexpected NULL pointer." );
}


static int threading_mutex_lock( mbedtls_threading_mutex_t * mutex )
{
    __CPROVER_assert( mutex != NULL, "Received an unexpected NULL pointer." );
    return nondet_bool() ? 0 : -1;
}

static int threading_mutex_unlock( mbedtls_threading_mutex_t * mutex )
{
    __CPROVER_assert( mutex != NULL, "Received an unexpected NULL pointer." );
    return nondet_bool() ? 0 : -1;
}

void (* mbedtls_mutex_init)( mbedtls_threading_mutex_t * ) = threading_mutex_init;
void (* mbedtls_mutex_free)( mbedtls_threading_mutex_t * ) = threading_mutex_free;
int (* mbedtls_mutex_lock)( mbedtls_threading_mutex_t * ) = threading_mutex_lock;
int (* mbedtls_mutex_unlock)( mbedtls_threading_mutex_t * ) = threading_mutex_unlock;

int mbedtls_cipher_cmac_finish( mbedtls_cipher_context_t * ctx,
                                unsigned char * output )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( output != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_havoc_object( output );

    return result;
}

int mbedtls_cipher_cmac_starts( mbedtls_cipher_context_t * ctx,
                                const unsigned char * key,
                                size_t keybits )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( key != NULL, "Received an unexpected NULL pointer." );

    return result;
}

int mbedtls_cipher_cmac_update( mbedtls_cipher_context_t * ctx,
                                const unsigned char * input,
                                size_t ilen )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( input != NULL, "Received an unexpected NULL pointer." );

    return result;
}

void mbedtls_cipher_free( mbedtls_cipher_context_t * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

const mbedtls_cipher_info_t * mbedtls_cipher_info_from_type( const mbedtls_cipher_type_t cipher_type )
{
    mbedtls_cipher_info_t * r = malloc( sizeof( mbedtls_cipher_info_t ) );

    return r;
}

int mbedtls_cipher_setup( mbedtls_cipher_context_t * ctx,
                          const mbedtls_cipher_info_t * cipher_info )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( cipher_info != NULL, "Received an unexpected NULL pointer." );

    return result;
}

int mbedtls_ecp_point_read_binary( const mbedtls_ecp_group * grp,
                                   mbedtls_ecp_point * P,
                                   const unsigned char * buf,
                                   size_t ilen )
{
    int result;

    __CPROVER_assert( grp != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( P != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( buf != NULL, "Received an unexpected NULL pointer." );

    return result;
}

int mbedtls_ecp_tls_write_point( const mbedtls_ecp_group * grp,
                                 const mbedtls_ecp_point * pt,
                                 int format,
                                 size_t * olen,
                                 unsigned char * buf,
                                 size_t blen )
{
    int result;

    __CPROVER_assert( grp != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( pt != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( olen != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( buf != NULL, "Received an unexpected NULL pointer." );

    return result;
}

void mbedtls_md_free( mbedtls_md_context_t * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

int mbedtls_md_hmac_finish( mbedtls_md_context_t * ctx,
                            unsigned char * output )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( output != NULL, "Received an unexpected NULL pointer." );

    return result;
}

int mbedtls_md_hmac_update( mbedtls_md_context_t * ctx,
                            const unsigned char * input,
                            size_t ilen )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( input != NULL, "Received an unexpected NULL pointer." );

    return result;
}

int mbedtls_mpi_read_binary( mbedtls_mpi * X,
                             const unsigned char * buf,
                             size_t buflen )
{
    int result;

    __CPROVER_assert( X != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( buf != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_havoc_object( X );

    return result;
}

void mbedtls_pk_free( mbedtls_pk_context * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

int mbedtls_pk_write_key_der( mbedtls_pk_context * ctx,
                              unsigned char * buf,
                              size_t size )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( buf != NULL, "Received an unexpected NULL pointer." );

    return result;
}

mbedtls_pk_type_t mbedtls_pk_get_type( const mbedtls_pk_context * ctx )
{
    mbedtls_pk_type_t result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );

    return result;
}

int mbedtls_pk_write_pubkey_der( mbedtls_pk_context * ctx,
                                 unsigned char * buf,
                                 size_t size )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( buf != NULL, "Received an unexpected NULL pointer." );

    return result;
}

void mbedtls_sha256_free( mbedtls_sha256_context * ctx )
{
    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
}

int mbedtls_sha256_update_ret( mbedtls_sha256_context * ctx,
                               const unsigned char * input,
                               size_t ilen )
{
    int result;

    __CPROVER_assert( ctx != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( input != NULL, "Received an unexpected NULL pointer." );

    return result;
}

void mbedtls_x509_crt_free( mbedtls_x509_crt * crt )
{
    __CPROVER_assert( crt != NULL, "Received an unexpected NULL pointer." );
}

int mbedtls_x509_crt_parse( mbedtls_x509_crt * chain,
                            const unsigned char * buf,
                            size_t buflen )
{
    int result;

    __CPROVER_assert( chain != NULL, "Received an unexpected NULL pointer." );
    __CPROVER_assert( buf != NULL, "Received an unexpected NULL pointer." );

    return result;
}
