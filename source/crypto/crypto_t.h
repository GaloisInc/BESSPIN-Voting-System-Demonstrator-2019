/**
 * SBB Crypto subsystem
 * @refine crypto.lando
 */

#ifndef __CRYPTO_T__
#define __CRYPTO_T__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#define AES_BLOCK_LENGTH_BITS 128
#define AES_BLOCK_LENGTH_BYTES (AES_BLOCK_LENGTH_BITS / 8)

#define AES128_KEY_LENGTH_BITS 128
#define AES128_KEY_LENGTH_BYTES (AES128_KEY_LENGTH_BITS / 8)
typedef uint8_t aes128_key[AES128_KEY_LENGTH_BYTES];

#define AES256_KEY_LENGTH_BITS 256
#define AES256_KEY_LENGTH_BYTES (AES256_KEY_LENGTH_BITS / 8)
typedef uint8_t aes256_key[AES256_KEY_LENGTH_BYTES];

#define SHA256_DIGEST_LENGTH_BITS 256
#define SHA256_DIGEST_LENGTH_BYTES (SHA256_DIGEST_LENGTH_BITS / 8)
typedef uint8_t sha256_digest[SHA256_DIGEST_LENGTH_BYTES];

typedef uint8_t* block;
typedef block plaintext_block;
typedef block ciphertext_block;
typedef uint8_t* digest;
typedef uint8_t* message;

// @note kiniry 256/8 = 32
typedef uint8_t sha_digest[32];

#endif
