# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY = harness
HARNESS_FILE = C_Verify_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = C_Verify

DEFINES +=
INCLUDES += -I$(SRCDIR)/3rdparty/mbedtls/include
INCLUDES += -I$(SRCDIR)/3rdparty/mbedtls_utils

REMOVE_FUNCTION_BODY +=
UNWINDSET += strlen.0:256
UNWINDSET += __CPROVER_file_local_core_pkcs11_mbedtls_c_prvGetKeyType.0:7

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/mbedtls_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/core_pkcs11_pal_stubs.c
PROJECT_SOURCES += $(SRCDIR)/source/portable/mbedtls/core_pkcs11_mbedtls.c

include ../Makefile.common
