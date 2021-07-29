/*
 * AWS IoT Device SDK for Embedded C
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
 * @file core_pkcs11_config_info.h
 * @brief File for documentation on corePKCS11 configurations.
 */


#ifndef CORE_PKCS11_CONFIG_INFO_H_
#define CORE_PKCS11_CONFIG_INFO_H_

/**
 * @brief Malloc API used by iot_pkcs11.h
 *
 * <br><b>Possible values:</b> Any platform-specific function for allocating memory.<br>
 * <b>Default value:</b> The standard C `"malloc"` function
 */
#ifdef DOXYGEN
    #define pkcs11configPKCS11_MALLOC    malloc
#endif

/**
 * @brief Free API used by iot_pkcs11.h
 *
 * <br><b>Possible values:</b> Any platform-specific function for freeing memory.<br>
 * <b>Default value:</b> The standard C `"free"` function
 */
#ifdef DOXYGEN
    #define pkcs11configPKCS11_FREE    free
#endif

/**
 * @brief PKCS #11 default user PIN.
 *
 * The PKCS #11 standard specifies the presence of a user PIN. That feature is
 * sensible for applications that have an interactive user interface and memory
 * protections. However, since typical microcontroller applications lack one or
 * both of those, the user PIN is assumed to be used herein for interoperability
 * purposes only, and not as a security feature.
 *
 * @note Do not cast this to a pointer! The library calls sizeof to get the length
 * of this string.
 *
 * <b>Possible values:</b> Any four digit code<br>
 * <b>Default value:</b> `"0000"`
 */
#ifdef DOXYGEN
    #define pkcs11configPKCS11_DEFAULT_USER_PIN    "0000"
#endif

/**
 * @brief Maximum length (in characters) for a PKCS #11 CKA_LABEL
 * attribute.
 *
 * <br><b>Possible values:</b> Any positive integer.<br>
 * <b>Default value:</b> `32`
 */
#ifdef DOXYGEN
    #define pkcs11configMAX_LABEL_LENGTH    32
#endif

/**
 * @brief Maximum number of token objects that can be stored
 * by the PKCS #11 module.
 *
 * <br><b>Possible values:</b> Any positive integer.<br>
 * <b>Default value:</b> `6`
 */
#ifdef DOXYGEN
    #define pkcs11configMAX_NUM_OBJECTS    6
#endif

/**
 * @brief Maximum number of sessions that can be stored
 * by the PKCS #11 module.
 *
 * @note The windows test port has an abnormally large value in order to have
 * enough sessions to successfully run all the model based PKCS #11 tests.
 *
 * <b>Possible values:</b> Any positive integer.<br>
 * <b>Default value:</b> 10
 */
#ifdef DOXYGEN
    #define pkcs11configMAX_SESSIONS    10
#endif


/**
 * @brief Set to 1 if a PAL destroy object is implemented.
 *
 * If set to 0, no PAL destroy object is implemented, and this functionality
 * is implemented in the common PKCS #11 layer.
 *
 * <b>Possible values:</b> `0` or `1`<br>
 * <b>Default value:</b> `0`
 */
#ifdef DOXYGEN
    #define pkcs11configPAL_DESTROY_SUPPORTED    0
#endif

/**
 * @brief Set to 1 if OTA image verification via PKCS #11 module is supported.
 *
 * If set to 0, OTA code signing certificate is built in via
 * aws_ota_codesigner_certificate.h.
 *
 * <b>Possible values:</b> `0` or `1`<br>
 * <b>Default value:</b> `0`
 */
#ifdef DOXYGEN
    #define pkcs11configOTA_SUPPORTED    0
#endif

/**
 * @brief Set to 1 if PAL supports storage for JITP certificate,
 * code verify certificate, and trusted server root certificate.
 *
 * If set to 0, PAL does not support storage mechanism for these, and
 * they are accessed via headers compiled into the code.
 *
 * <b>Possible values:</b> `0` or `1`<br>
 * <b>Default value:</b> `0`
 */
#ifdef DOXYGEN
    #define pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED    0
#endif

/**
 * @brief The PKCS #11 label for device private key.
 *
 * Private key for connection to AWS IoT endpoint.  The corresponding
 * public key should be registered with the AWS IoT endpoint.
 *
 * <b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `Device Priv TLS Key`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS    "Device Priv TLS Key"
#endif

/**
 * @brief The PKCS #11 label for device public key.
 *
 * The public key corresponding to pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS.
 *
 * <b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `Device Pub TLS Key`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS    "Device Pub TLS Key"
#endif

/**
 * @brief The PKCS #11 label for the device certificate.
 *
 * Device certificate corresponding to pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS.
 *
 * <b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `Device Cert`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS    "Device Cert"
#endif

/**
 * @brief The PKCS #11 label for the AWS Trusted Root Certificate.
 *
 * @see aws_default_root_certificates.h
 *
 * <b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `Root Cert`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_ROOT_CERTIFICATE    "Root Cert"
#endif

/**
 * @brief The PKCS #11 label for the object to be used for HMAC operations.
 *
 * <br><b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `HMAC Key`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_HMAC_KEY    "HMAC Key"
#endif

/**
 * @brief The PKCS #11 label for the object to be used for CMAC operations.
 *
 * <br><b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `CMAC Key`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_CMAC_KEY    "CMAC Key"
#endif

/**
 * @brief The PKCS #11 label for the object to be used for code verification.
 *
 * Used by AWS IoT Over-the-Air Update (OTA) code to verify an incoming signed image.
 *
 * <b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `Code Verify Key`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_CODE_VERIFICATION_KEY    "Code Verify Key"
#endif

/**
 * @brief The PKCS #11 label for AWS IoT Just-In-Time-Provisioning.
 *
 * The certificate corresponding to the issuer of the device certificate
 * (pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS) when using the JITR or
 * JITP flow.
 *
 * <b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `Code Verify Key`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_JITP_CERTIFICATE    "JITP Cert"
#endif

/**
 * @brief The PKCS #11 label for the object to be used for code verification.
 *
 * Used by AWS IoT Over-the-Air Update (OTA) code to verify an incoming signed image.
 *
 * <b>Possible values:</b> Any String smaller then pkcs11configMAX_LABEL_LENGTH.<br>
 * <b>Default value:</b> `Code Verify Key`
 */
#ifdef DOXYGEN
    #define pkcs11configLABEL_CODE_VERIFICATION_KEY    "Code Verify Key"
#endif

/**
 * @brief Macro that is called in the corePKCS11 library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the corePKCS11 library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the corePKCS11 library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant.
 * For a reference implementation of the logging macros in POSIX environment,
 * refer to core_pkcs11_config.h files, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifdef DOXYGEN
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the corePKCS11 library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the corePKCS11 library, this macro should be mapped to the
 * application-specific logging implementation that supports warning logging.
 *
 * @note This logging macro is called in the corePKCS11 library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant.
 * For a reference implementation of the logging macros in POSIX environment,
 * refer to core_pkcs11_config.h files, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifdef DOXYGEN
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the corePKCS11 library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the corePKCS11 library, this macro should be mapped to the
 * application-specific logging implementation that supports info logging.
 *
 * @note This logging macro is called in the corePKCS11 library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant.
 * For a reference implementation of the logging macros in POSIX environment,
 * refer to core_pkcs11_config.h files, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifdef DOXYGEN
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the corePKCS11 library for logging "Debug" level
 * messages.
 *
 * To enable debug level logging from corePKCS11 library, this macro should be mapped to the
 * application-specific logging implementation that supports debug logging.
 *
 * @note This logging macro is called in the corePKCS11 library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant.
 * For a reference implementation of the logging macros in POSIX environment,
 * refer to core_pkcs11_config.h files, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifdef DOXYGEN
    #define LogDebug( message )
#endif

#endif /* _AWS_PKCS11_CONFIG_H_ include guard. */
