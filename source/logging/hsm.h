/**
 * Placeholder API for Hardware Security Module/Crypto Processor
 * 
 * Provides abstraction of basic crypto functions.
 * Initially, this will be implemented in software.
 * Later, this will be implemented by HSM hardware as and when it becomes available.
 */

#ifndef __HSM_T__
#define __HSM_T__

#include <stdint.h>
#include <stddef.h>
#include "../crypto/crypto_t.h"

#define AES128_KEY_LENGTH_BITS 128
#define AES128_KEY_LENGTH_BYTES (AES128_KEY_LENGTH_BITS / 8)
typedef uint8_t aes128_key[AES128_KEY_LENGTH_BYTES];

#define AES256_KEY_LENGTH_BITS 256
#define AES256_KEY_LENGTH_BYTES (AES256_KEY_LENGTH_BITS / 8)
typedef uint8_t aes256_key[AES256_KEY_LENGTH_BYTES];

#define SHA256_DIGEST_LENGTH_BITS 256
#define SHA256_DIGEST_LENGTH_BYTES (SHA256_DIGEST_LENGTH_BITS / 8)
typedef uint8_t sha256_digest[SHA256_DIGEST_LENGTH_BYTES];

#define BVS2019_AES_KEY_LENGTH_BITS AES128_KEY_LENGTH_BITS 
#define BVS2019_AES_KEY_LENGTH_BYTES AES128_KEY_LENGTH_BYTES

#define BVS2019_SHA_DIGEST_LENGTH_BITS SHA256_DIGEST_LENGTH_BITS
#define BVS2019_SHA_DIGEST_LENGTH_BYTES SHA256_DIGEST_LENGTH_BYTES

/*@ requires \valid_read(the_plaintext + (0 .. AES_BLOCK_SIZE - 1));
  @ requires \valid(the_ciphertext + (0 .. AES_BLOCK_SIZE - 1));
  @ requires \separated(the_plaintext, the_ciphertext);
  @ assigns the_ciphertext[0 .. AES_BLOCK_SIZE - 1];
  @ ensures lift_ciphertext(the_ciphertext) ==
  @         encrypt(lift_plaintext(the_plaintext));
  @ ensures decrypt(encrypt(lift_plaintext(the_plaintext))) ==
  @         lift_ciphertext(the_ciphertext);
  @*/
void aes_encrypt_block(plaintext_block  the_plaintext,
                       ciphertext_block the_ciphertext);

/*@ requires \valid_read(the_ciphertext + (0 .. AES_BLOCK_SIZE - 1));
  @ requires \valid(the_plaintext + (0 .. AES_BLOCK_SIZE - 1));
  @ requires \separated(the_ciphertext, the_plaintext);
  @ assigns the_plaintext[0 .. AES_BLOCK_SIZE - 1];
  @ ensures lift_plaintext(the_plaintext) ==
  @         decrypt(lift_ciphertext(the_ciphertext));
  @ ensures encrypt(decrypt(lift_ciphertext(the_ciphertext))) ==
  @         lift_plaintext(the_plaintext);
  @*/
void aes_decrypt_block(ciphertext_block the_ciphertext,
                       plaintext_block  the_plaintext);

/*@ requires \valid_read(key + (0 .. AES256_KEY_LENGTH_BYTES - 1));
  @ requires \valid_read(msg + (0 .. msg_size - 1));
  @ requires \separated(key, msg, digest);
  @ assigns digest[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
  @ ensures \valid(digest + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
  @*/
// @design kiniry Shouldn't the type for `msg` be `message` from `crypto_t.h`?
void hmac(const aes256_key key,      // IN
	  const char       msg[],    // IN
	  const size_t     msg_size, // IN
          digest           digest);  // OUT

/*@ requires \valid_read(msg + (0 .. msg_size - 1));
  @ requires \separated(msg, digest);
  @ assigns digest[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
  @ ensures \valid (digest + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
  @*/
// @review kiniry When do we use `[]` vs. `*`?
// @review kiniry Much like `hmac`, reflect on choice of types in
// formal parameters.
// @review kiniry In vs. out parameters are denoted via an `assigns`
// clause in a function's contract.  Having a second hint about such,
// either in formal parameter names (such as `in_msg`) or comments, as
// is done below, is a possibility.  We should reflect on what we want
// overall in our coding standard, given we are currently using three
// different convensions for such.
void sha256(const uint8_t msg[],     // IN
	    const size_t  msg_size,  // IN
            digest        digest);   // OUT

#endif
