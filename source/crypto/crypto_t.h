/**
 * SBB Crypto subsystem
 * @refine crypto.lando
 */

#ifndef __CRYPTO_T__
#define __CRYPTO_T__

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define AES_BLOCK_LENGTH_BITS 128
#define AES_BLOCK_LENGTH_BYTES (AES_BLOCK_LENGTH_BITS / 8)
#define BASE_64_AES_BLOCK_LENGTH_BYTES 24
typedef uint8_t aes128_block[AES_BLOCK_LENGTH_BYTES];
typedef uint8_t base64_aes128_block[BASE_64_AES_BLOCK_LENGTH_BYTES];

// Whole array assignment of src[0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1] to
//                           dst[0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1]

/*@ requires \valid(dst + (0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1));
    requires \valid_read(src + (0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1));
    requires \separated(dst + (0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1),
                        src + (0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1));
    assigns dst[0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1];
    ensures \forall integer i; 0 <= i < BASE_64_AES_BLOCK_LENGTH_BYTES ==> dst[i] == src[i];
*/
void copy_base64_aes128_block (base64_aes128_block dst,  // OUT
      	                       base64_aes128_block src); // IN


#define AES128_KEY_LENGTH_BITS 128
#define AES128_KEY_LENGTH_BYTES (AES128_KEY_LENGTH_BITS / 8)
typedef uint8_t aes128_key[AES128_KEY_LENGTH_BYTES];

#define AES256_KEY_LENGTH_BITS 256
#define AES256_KEY_LENGTH_BYTES (AES256_KEY_LENGTH_BITS / 8)
typedef uint8_t aes256_key[AES256_KEY_LENGTH_BYTES];

#define SHA256_DIGEST_LENGTH_BITS 256
#define SHA256_DIGEST_LENGTH_BYTES (SHA256_DIGEST_LENGTH_BITS / 8)
typedef uint8_t sha256_digest[SHA256_DIGEST_LENGTH_BYTES];

typedef uint8_t *block;
typedef block plaintext_block;
typedef block ciphertext_block;
typedef uint8_t *digest;
typedef uint8_t *message;

typedef uint8_t sha_digest[SHA256_DIGEST_LENGTH_BYTES];

// Names for a set of keys that can be used with AES encrypt, decrypt, or MAC
typedef enum { Barcode_MAC_Key = 0,
               Log_Root_Block_MAC_Key,
               Log_Entry_MAC_Key,
               Mock_Key } AES_Key_Name;

#endif // __CRYPTO_T__
