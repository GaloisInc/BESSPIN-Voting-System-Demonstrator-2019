/**
 * SBB Crypto subsystem
 * @refine crypto.lando
 */

#ifndef __CRYPTO_T__
#define __CRYPTO_T__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

// All sizes in bits.

const uint32_t AES_BLOCK_SIZE  = 256;
const uint32_t AES_KEY_SIZE    = 256;
const uint32_t SHA_DIGEST_SIZE = 256;

typedef uint8_t* block;
typedef block plaintext_block;
typedef block ciphertext_block;
typedef uint8_t* digest;
typedef uint8_t* message;

// @note kiniry 256/8 = 32

typedef uint8_t aes_block[32];
typedef uint8_t sha_digest[32];

#endif
