#ifndef __CONFIG_CUSTOM_MBEDTLS_H__
#define __CONFIG_CUSTOM_MBEDTLS_H__

#define MBEDTLS_THREADING_C
#define MBEDTLS_THREADING_ALT

#undef MBEDTLS_NO_DEFAULT_ENTROPY_SOURCES
#define MBEDTLS_ENTROPY_HARDWARE_ALT

#define MBEDTLS_CIPHER_MODE_CTR

#define MBEDTLS_PKCS1_V21

#define MBEDTLS_X509_CRL_PARSE_C
#define MBEDTLS_X509_CHECK_KEY_USAGE
#define MBEDTLS_X509_CHECK_EXTENDED_KEY_USAGE

#endif /* __CONFIG_CUSTOM_MBEDTLS_H__ */
