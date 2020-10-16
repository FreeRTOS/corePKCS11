# Change Log for corePKCS11 Library

## v2.0.1 (September 2020)
* Replaced *iot* prefix on files with *core* prefix.

## v2.0.0 (September 2020)
This is the first release of the corePKCS11 library in this repository.

This library is a software based implementation of the PKCS #11 specification.

* PKCS #11 library is now decoupled from the FreeRTOS-Kernel, and instead uses mutex and heap function abstractions provided by mbed TLS.
* The PKCS #11 library logging has been overhauled and is now decoupled from FreeRTOS.
* Added `PKCS11_PAL_Initialize` to `core_pkcs11_pal.h` to defer PAL layer initialization to PKCS #11 PAL.

