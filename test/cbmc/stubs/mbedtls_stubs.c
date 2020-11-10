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
 * @file mbedtls_stubs.c
 * @brief Stubs for mbed TLS functions.
 */

#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/threading.h"


void mbedtls_entropy_init( mbedtls_entropy_context *ctx )
{
    ( void ) ctx;
}

void mbedtls_entropy_free( mbedtls_entropy_context *ctx )
{
    ( void ) ctx;
}

void mbedtls_ctr_drbg_init( mbedtls_ctr_drbg_context *ctx )
{
    ( void ) ctx;
}

int mbedtls_ctr_drbg_seed( mbedtls_ctr_drbg_context *ctx,
                   int (*f_entropy)(void *, unsigned char *, size_t),
                   void *p_entropy,
                   const unsigned char *custom,
                   size_t len )
{
    return 0;
}

void mbedtls_ctr_drbg_free( mbedtls_ctr_drbg_context *ctx )
{
    ( void ) ctx;
}

static void threading_mutex_init( mbedtls_threading_mutex_t * mutex )
{
    ( void ) mutex;
}

static void threading_mutex_free( mbedtls_threading_mutex_t * mutex )
{
    ( void ) mutex;
}


static int threading_mutex_lock( mbedtls_threading_mutex_t * mutex )
{
    return 0;
}

static int threading_mutex_unlock( mbedtls_threading_mutex_t * mutex )
{
    return 0;
}

void (* mbedtls_mutex_init)( mbedtls_threading_mutex_t * ) = threading_mutex_init;
void (* mbedtls_mutex_free)( mbedtls_threading_mutex_t * ) = threading_mutex_free;
int (* mbedtls_mutex_lock)( mbedtls_threading_mutex_t * ) = threading_mutex_lock;
int (* mbedtls_mutex_unlock)( mbedtls_threading_mutex_t * ) = threading_mutex_unlock;

