cmake_minimum_required(VERSION 3.15)

project(corePKCS11 LANGUAGES C)

# ------------------------------------------------------------------------------
# Includes
# ------------------------------------------------------------------------------

include(${CMAKE_CURRENT_LIST_DIR}/pkcsFilePaths.cmake)

# ------------------------------------------------------------------------------
# Library targets
# ------------------------------------------------------------------------------

add_library( core_pkcs )


target_sources( core_pkcs PUBLIC ${PKCS_SOURCES}
                                      ${PKCS_PAL_POSIX_SOURCES} )

target_include_directories( core_pkcs PUBLIC ${PKCS_INCLUDE_PUBLIC_DIRS}
                                             ${PKCS_PAL_INCLUDE_PUBLIC_DIRS} )

if(TEST_BUILD)
    include(FetchContent)

    FetchContent_Declare( pkcs11
        GIT_REPOSITORY https://github.com/oasis-tcs/pkcs11.git
        GIT_TAG        478bfc5077901865993e3a193777c1a9f6516cdf
    )
    FetchContent_MakeAvailable( pkcs11 )

    FetchContent_Declare( mbedtls
        GIT_REPOSITORY https://github.com/Mbed-TLS/mbedtls.git
        GIT_TAG        mbedtls-3.6.5
    )
    FetchContent_MakeAvailable( mbedtls )

    target_include_directories( core_pkcs PUBLIC ${CMAKE_CURRENT_LIST_DIR}/test/include
    ${pkcs11_SOURCE_DIR}/published/2-40-errata-1
    ${mbedtls_SOURCE_DIR}/include
    ${mbedtls_SOURCE_DIR}/library
    ${mbedtls_SOURCE_DIR}/include/mbedtls )
endif()
