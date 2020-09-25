# FreeRTOS PKCS #11 Library

This repository contains a software based PKCS #11 library to enable rapid development and flexibility when developing libraries and platforms that rely on crypto operations.

## Building Unit Tests.

### PKCS Config File

The PKCS #11 library exposes build configuration macros that are required for building the library.
A list of all the configurations and their default values are defined in the doxygen documentation for this library.

### Platform Prerequisites

- For building the library, **CMake 3.13.0 or later** and a **C90 compiler**.
- For running unit tests, Ruby 2.0.0 or later is additionally required for the CMock test framework (that we use).
- For running the coverage target, gcov is additionally required.

### Steps to build **Library** and **Unit Tests**

1. Go to the root directory of this repository.

1. Run *cmake* while inside build directory: `cmake -S ../test/unit-test -B build -DBUILD_CLONE_SUBMODULES=ON `

1. Run this command to build the library and unit tests: `make -C build all`

1. The built library will be present in `build/lib` folder, and generated test executables will be present in `build/bin/tests` folder.

1. Run `ctest` to execute all tests and view the test run summary.

## Reference examples

The FreeRTOS-Labs repository contains demos using the PKCS #11 library [here](https://github.com/FreeRTOS/FreeRTOS-Labs/tree/master/FreeRTOS-Plus/Demo/FreeRTOS_Plus_PKCS11_Windows_Simulator/examples) using FreeRTOS on the Windows simulator platform. These can be used as reference examples for the library API.

## Generating documentation

The Doxygen references were created using Doxygen version 1.8.20. To generate the
Doxygen pages, please run the following command from the root of this repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This library is licensed under the MIT-0 License. See the LICENSE file.

