/* 
 * corePKCS11 v2.0.0
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
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file core_pkcs11_config_defaults.h
 * @brief This represents the default values for the configuration macros
 * for the corePKCS11 library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, a core_pkcs11_config.h file should be provided to
 * the corePKCS11 library to override the default values defined in this file.
 * To use the custom config file, the CORE_PKCS11_DO_NOT_USE_CUSTOM_CONFIG preprocessor
 * macro SHOULD NOT be set.
 */

#ifndef _CORE_PKCS11_CONFIG_DEFAULTS_H_
#define _CORE_PKCS11_CONFIG_DEFAULTS_H_

/* The macro definition for CORE_PKCS11_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the corePKCS11 library without the custom config
 * file core_pkcs11_config.h.
 *
 * Without the custom config, the corePKCS11 library builds with
 * default values of config macros defined in core_pkcs11_config_defaults.h file.
 *
 * If a custom config is provided, then CORE_PKCS11_DO_NOT_USE_CUSTOM_CONFIG should not
 * be defined.
 */
#ifdef DOXYGEN
    #define CORE_PKCS11_DO_NOT_USE_CUSTOM_CONFIG
#endif

/**
 * @brief Malloc API used by core_pkcs11.h
 */
#define PKCS11_MALLOC    malloc

/**
 * @brief Free API used by core_pkcs11.h
 */
#define PKCS11_FREE      free


/**
 * @brief PKCS #11 default user PIN.
 *
 * The PKCS #11 standard specifies the presence of a user PIN. That feature is
 * sensible for applications that have an interactive user interface and memory
 * protections. However, since typical microcontroller applications lack one or
 * both of those, the user PIN is assumed to be used herein for interoperability
 * purposes only, and not as a security feature.
 */
#define configPKCS11_DEFAULT_USER_PIN                      "0000"

/**
 * @brief Maximum length (in characters) for a PKCS #11 CKA_LABEL
 * attribute.
 */
#define pkcs11configMAX_LABEL_LENGTH                       32

/**
 * @brief Maximum number of token objects that can be stored
 * by the PKCS #11 module.
 */
#define pkcs11configMAX_NUM_OBJECTS                        6

/**
 * @brief Maximum number of sessions that can be stored
 * by the PKCS #11 module.
 */
#define pkcs11configMAX_SESSIONS                           10

/**
 * @brief Set to 1 if a PAL destroy object is implemented.
 *
 * If set to 0, no PAL destroy object is implemented, and this functionality
 * is implemented in the common PKCS #11 layer.
 */
#define pkcs11configPAL_DESTROY_SUPPORTED                  0

/**
 * @brief Set to 1 if OTA image verification via PKCS #11 module is supported.
 *
 * If set to 0, OTA code signing certificate is built in via
 * aws_ota_codesigner_certificate.h.
 */
#define pkcs11configOTA_SUPPORTED                          0

/**
 * @brief Set to 1 if PAL supports storage for JITP certificate,
 * code verify certificate, and trusted server root certificate.
 *
 * If set to 0, PAL does not support storage mechanism for these, and
 * they are accessed via headers compiled into the code.
 */
#define pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED    0

/**
 * @brief The PKCS #11 label for device private key.
 *
 * Private key for connection to AWS IoT endpoint.  The corresponding
 * public key should be registered with the AWS IoT endpoint.
 */
#define pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS       "Device Priv TLS Key"

/**
 * @brief The PKCS #11 label for device public key.
 *
 * The public key corresponding to pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS.
 */
#define pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS        "Device Pub TLS Key"

/**
 * @brief The PKCS #11 label for the device certificate.
 *
 * Device certificate corresponding to pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS.
 */
#define pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS       "Device Cert"

/**
 * @brief The PKCS #11 label for the object to be used for code verification.
 *
 * Used by over-the-air update code to verify an incoming signed image.
 */
#define pkcs11configLABEL_CODE_VERIFICATION_KEY            "Code Verify Key"

/**
 * @brief The PKCS #11 label for Just-In-Time-Provisioning.
 *
 * The certificate corresponding to the issuer of the device certificate
 * (pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS) when using the JITR or
 * JITP flow.
 */
#define pkcs11configLABEL_JITP_CERTIFICATE                 "JITP Cert"

/**
 * @brief The PKCS #11 label for the AWS Trusted Root Certificate.
 *
 * @see aws_default_root_certificates.h
 */
#define pkcs11configLABEL_ROOT_CERTIFICATE                 "Root Cert"

/**
 * @brief Macro that is called in the corePKCS11 library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the corePKCS11 library, this macro should be mapped to the
 * application-specific logging implementation that supports error logging.
 *
 * @note This logging macro is called in the corePKCS11 library with parameters wrapped in
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_pkcs11_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifndef LogError
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
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_pkcs11_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifndef LogWarn
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
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_pkcs11_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifndef LogInfo
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
 * double parentheses to be ISO C89/C90 standard compliant. For a reference
 * POSIX implementation of the logging macros, refer to core_pkcs11_config.h files, and the
 * logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated for calls
 * to the macro in the corePKCS11 library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

#endif /* ifndef _CORE_PKCS11_CONFIG_DEFAULTS_H_ */ 
