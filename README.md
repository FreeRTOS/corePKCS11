# corePKCS11 Library
[PKCS #11](https://en.wikipedia.org/wiki/PKCS_11) is a standardised and widely used API for manipulating common cryptographic objects. It is important because the functions it specifies allow application software to use, create, modify, and delete cryptographic objects, without ever exposing those objects to the application’s memory.
For example, FreeRTOS AWS reference integrations use a small subset of the PKCS #11 API to, among other things, access the secret (private) key necessary to create a network connection that is authenticated and secured by the [Transport Layer Security (TLS)](https://en.wikipedia.org/wiki/Transport_Layer_Security) protocol – without the application ever ‘seeing’ the key.


The Cryptoki or PKCS #11 standard defines a platform-independent API to manage and use cryptographic tokens. The name, "PKCS #11", is used interchangeably to refer to the API itself and the standard which defines it.

This repository contains a software based mock implementation of the PKCS #11 interface (API) that uses the cryptographic functionality provided by Mbed TLS. Using a software mock enables rapid development and flexibility, but it is expected that the mock be replaced by an implementation specific to your chosen secure key storage in production devices.

Only a subset of the PKCS #11 standard is implemented, with a focus on operations involving asymmetric keys, random number generation, and hashing.

The targeted use cases include certificate and key management for TLS authentication and code-sign signature verification, on small embedded devices.

corePKCS11 is implemented on PKCS #11 v2.4.0, the full PKCS #11 standard can be found on the [oasis website](http://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html).

This library has gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score over 8, and checks against deviations from mandatory rules in the [MISRA coding standard](https://www.misra.org.uk).  Deviations from the MISRA C:2012 guidelines are documented under [MISRA Deviations](MISRA.md). This library has also undergone both static code analysis from [Coverity static analysis](https://scan.coverity.com/) and validation of memory safety through the [CBMC automated reasoning tool](https://www.cprover.org/cbmc/).

See memory requirements for this library [here](./docs/doxygen/include/size_table.md).

**corePKCS11 v3.0.0 [source code](https://github.com/FreeRTOS/corePKCS11/tree/v3.0.0/source) is part of the [FreeRTOS 202012.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202012.00-LTS) release.**

# Purpose

Generally vendors for secure cryptoprocessors such as Trusted Platform Module ([TPM](https://en.wikipedia.org/wiki/Trusted_Platform_Module)), Hardware Security Module ([HSM](https://en.wikipedia.org/wiki/Hardware_security_module)), Secure Element, or any other type of secure hardware enclave, distribute a PKCS #11 implementation with the hardware.
The purpose of the corePKCS11 software only mock library is therefore to provide a non hardware specific PKCS #11 implementation that allows for rapid prototyping and development before switching to a cryptoprocessor specific PKCS #11 implementation in production devices.

Since the PKCS #11 interface is defined as part of the PKCS #11 [specification](https://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html) replacing this library with another implementation should require little porting effort, as the interface will not change. The system tests distributed in this repository can be leveraged to verify the behavior of a different implementation is similar to corePKCS11.

## Building Unit Tests.

### PKCS Config File

The PKCS #11 library exposes build configuration macros that are required for building the library.
A list of all the configurations and their default values are defined in the doxygen documentation for this library.

### Platform Prerequisites

- For building the library, **CMake 3.13.0 or later** and a **C99 compiler**.
- For running unit tests, Ruby 2.0.0 or later is additionally required for the CMock test framework (that we use).
- For running the coverage target, gcov is additionally required.

### Steps to build **Library** and **Unit Tests**

### Checkout CMock Submodule
By default, the submodules in this repository are configured with `update=none` in [.gitmodules](.gitmodules) to avoid increasing clone time and disk space usage of other repositories (like [amazon-freertos](https://github.com/aws/amazon-freertos) that submodule this repository.

To build unit tests, the submodule dependency of CMock is required. Use the following command to clone the submodule:
```
git submodule update --checkout --init --recursive test/unit-test/CMock
```

1. Go to the root directory of this repository. (Make sure that the **CMock** submodule is cloned as described [above](#checkout-cmock-submodule))

1. Create the build directory: `mkdir build`

1. Enter the build directory: `cd build`

1. Run *cmake* while inside build directory: `cmake -S ../test -DUNIT_TESTS=1`

1. Run this command to build the library and unit tests: `make all`

1. The built library will be present in `build/lib` folder, and generated test executables will be present in `build/bin/tests` folder.

1. Run `ctest` to execute all tests and view the test run summary.

## Reference examples

The FreeRTOS-Labs repository contains demos using the PKCS #11 library [here](https://github.com/FreeRTOS/FreeRTOS-Labs/tree/master/FreeRTOS-Plus/Demo/FreeRTOS_Plus_PKCS11_Windows_Simulator/examples) using FreeRTOS on the Windows simulator platform. These can be used as reference examples for the library API.

## Porting Guide
Documentation for porting corePKCS11 to a new platform can be found on the AWS [docs](https://docs.aws.amazon.com/freertos/latest/portingguide/afr-porting-pkcs.html) web page.

corePKCS11 is not meant to be ported to projects that have a TPM, HSM, or other hardware for offloading crypto-processing. This library is specifically meant to be used for development and prototyping.


## Related Example Implementations
These projects implement the PKCS #11 interface on real hardware and have similar behavior to corePKCS11. It is preferred to use these, over corePKCS11, as they allow for offloading Cryptography to separate hardware.

* ARM's [Platform Security Architecture](https://github.com/Linaro/freertos-pkcs11-psa).
* Microchip's [cryptoauthlib](https://github.com/MicrochipTech/cryptoauthlib).
* Infineon's [Optiga Trust X](https://github.com/aws/amazon-freertos/blob/main/vendors/infineon/secure_elements/pkcs11/iot_pkcs11_trustx.c).

## Documentation

### Existing Documentation
For pre-generated documentation, please see the documentation linked in the locations below:

| Location |
| :-: |
| [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C#releases-and-documentation) |
| [FreeRTOS.org](https://freertos.org/Documentation/api-ref/corePKCS11/docs/doxygen/output/html/index.html) |

Note that the latest included version of corePKCS11 may differ across repositories.

### Generating Documentation
The Doxygen references were created using Doxygen version 1.9.2. To generate the
Doxygen pages, please run the following command from the root of this repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This library is licensed under the MIT-0 License. See the LICENSE file.

