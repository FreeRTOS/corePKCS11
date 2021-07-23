# Change Log for corePKCS11 Library

## v3.1.0 (July 2021)
- [#119](https://github.com/FreeRTOS/corePKCS11/pull/119) Update mbedTLS submodule to [v2.26.0](https://github.com/ARMmbed/mbedtls/tree/v2.26.0).
* [#118](https://github.com/FreeRTOS/corePKCS11/pull/118) Update version numbers and add C++ header guards
* [#116](https://github.com/FreeRTOS/corePKCS11/pull/116) Remove redundant mbedtls error sources
* [#115](https://github.com/FreeRTOS/corePKCS11/pull/115) Update broken links to MISRA in documentation
* [#113](https://github.com/FreeRTOS/corePKCS11/pull/113) Fix description of CBMC in README
* [#112](https://github.com/FreeRTOS/corePKCS11/pull/112) Add additional validation of the return value of mbedtls_pk_write_*_der functions
* [#111](https://github.com/FreeRTOS/corePKCS11/pull/111) Add AES-CMAC algorithm support in Windows port
* [#110](https://github.com/FreeRTOS/corePKCS11/pull/110) Hygiene fixes in CI checks
* [#104](https://github.com/FreeRTOS/corePKCS11/pull/104) Minor MISRA fixes
* [#103](https://github.com/FreeRTOS/corePKCS11/pull/103) Fix doxygen main page generation
* [#102](https://github.com/FreeRTOS/corePKCS11/pull/102) Feature: AES CMAC Sign/SignInit
* [#101](https://github.com/FreeRTOS/corePKCS11/pull/101) Feature: AES CMAC - VerifyInit/Verify
* [#98](https://github.com/FreeRTOS/corePKCS11/pull/98) Fix MISRA regressions
* [#97](https://github.com/FreeRTOS/corePKCS11/pull/97) Implement C_CreateObject for AES CMAC keys
* [#96](https://github.com/FreeRTOS/corePKCS11/pull/96) Feature: SHA256-HMAC sign
* [#95](https://github.com/FreeRTOS/corePKCS11/pull/95) Feature: SHA256-HMAC C_SignInit
* [#94](https://github.com/FreeRTOS/corePKCS11/pull/94) Fix system test output suppresion
* [#91](https://github.com/FreeRTOS/corePKCS11/pull/91) Fix potential double free in core_pkcs11.c
* [#86](https://github.com/FreeRTOS/corePKCS11/pull/86) Feature: SHA256-HMAC VerifyInit
* [#84](https://github.com/FreeRTOS/corePKCS11/pull/84) Feature: Import SHA256-HMAC secret Key

## v3.0.1 (February 2021)
* Removed default `PKCS11_PAL_DestroyObject` implementation from `core_pkcs11_mbedtls.c`. [#74](https://github.com/FreeRTOS/corePKCS11/pull/74). This means that all PAL ports must implement `PKCS11_PAL_DestroyObject`.

## v3.0.0 (December 2020)
* Changed `xFindObjectWithLabelAndClass` to include a size parameter to allow the caller to specify the size of the passed in label.
* Added CBMC memory proofs for all functions
* Removed `threading_alt.h` from corePKCS11
* Restructured third party folder in order to align with other core repositories. Folders located in `corePKCS11/3rdparty` are now in `corePKCS11/source/dependency/3rdparty`.
* Updated logs and format specifiers to use standard C types.
* Added a POSIX PAL port.

## v2.0.1 (September 2020)
* Replaced *iot* prefix on files with *core* prefix.

## v2.0.0 (September 2020)
This is the first release of the corePKCS11 library in this repository.

This library is a software based implementation of the PKCS #11 specification.

* PKCS #11 library is now decoupled from the FreeRTOS-Kernel, and instead uses mutex and heap function abstractions provided by mbed TLS.
* The PKCS #11 library logging has been overhauled and is now decoupled from FreeRTOS.
* Added `PKCS11_PAL_Initialize` to `core_pkcs11_pal.h` to defer PAL layer initialization to PKCS #11 PAL.
