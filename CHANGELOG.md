# Change Log for FreeRTOS-PKCS Library

## v2.0.0 09/2020
This is the first release of the FreeRTOS-PKCS library in this repository.
This library is a software based implementation of the PKCS #11 specification.
PKCS #11 library is now decoupled from the FreeRTOS-Kernel, and instead uses mutex and heap function abstractions provided by mbed TLS.
Compliance to the FreeRTOS LTS release standards found (here)[https://www.freertos.org/ltsroadmap.html].
The PKCS #11 library logging has been overhauled and is now decoupled from FreeRTOS.
Added `PKCS11_PAL_Initialize` to `iot_pkcs11_pal.h` to defer PAL layer initialization to PKCS #11 PAL.

