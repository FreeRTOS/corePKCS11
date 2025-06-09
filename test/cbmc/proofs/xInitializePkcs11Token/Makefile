# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = harness
HARNESS_FILE = xInitializePkcs11Token_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = xInitializePkcs11Token

DEFINES +=

INCLUDES += -I$(SRCDIR)/test/build/_deps/mbedtls_2-src/include

CBMC_OBJECT_BITS = 10

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/pkcs11_interface_stubs.c
PROJECT_SOURCES += $(SRCDIR)/source/core_pkcs11.c
PROJECT_SOURCES += $(SRCDIR)/source/portable/mbedtls/core_pkcs11_mbedtls.c

include ../Makefile.common
