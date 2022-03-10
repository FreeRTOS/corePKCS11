#!/bin/sh
MBEDTLS_DIR="${1}"
CONFIG="${2}"

cp $MBEDTLS_DIR/include/mbedtls/$CONFIG mbedtls_config_patch.h
$MBEDTLS_DIR/scripts/config.py --file mbedtls_config_patch.h full_no_deprecated
$MBEDTLS_DIR/scripts/config.py --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_BUILTIN_KEYS
$MBEDTLS_DIR/scripts/config.py --file mbedtls_config_patch.h unset MBEDTLS_ENTROPY_NV_SEED
$MBEDTLS_DIR/scripts/config.py --file mbedtls_config_patch.h unset MBEDTLS_PLATFORM_NV_SEED_ALT
cmp --quiet $MBEDTLS_DIR/include/mbedtls/config.h mbedtls_config_patch.h || {
    cp mbedtls_config_patch.h $MBEDTLS_DIR/include/mbedtls/$CONFIG
}
