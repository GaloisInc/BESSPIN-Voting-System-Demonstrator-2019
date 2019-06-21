/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

#ifndef __CRYPTO_H__
#define __CRYPTO_H__

// General includes
#include <stdbool.h>
#include <stdint.h>

// Subsystem includes
#include "crypto.acsl"
#include "crypto_t.h"

/*@ requires \valid_read(the_plaintext + (0 .. AES_BLOCK_LENGTH_BYTES - 1));
  @ requires \valid(the_ciphertext + (0 .. AES_BLOCK_LENGTH_BYTES - 1));
  @ requires \separated(the_plaintext, the_ciphertext);
  @ assigns the_ciphertext[0 .. AES_BLOCK_LENGTH_BYTES - 1];
  @*/
void encrypt(plaintext_block the_plaintext, ciphertext_block the_ciphertext);

/*@ requires \valid_read(the_ciphertext + (0 .. AES_BLOCK_LENGTH_BYTES - 1));
  @ requires \valid(the_plaintext + (0 .. AES_BLOCK_LENGTH_BYTES - 1));
  @ requires \separated(the_plaintext, the_ciphertext);
  @ assigns the_plaintext[0 .. AES_BLOCK_LENGTH_BYTES - 1];
  @*/
void decrypt(ciphertext_block the_ciphertext, plaintext_block the_plaintext);

/*@ requires \valid_read(the_message + (0 .. the_message_size - 1));
  @ requires \valid(the_digest + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
  @ requires \separated(the_message, the_digest);
  @ assigns the_digest[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
  @*/
void hash(message the_message, size_t the_message_size, digest the_digest);

/*@ requires \valid_read(the_message + (0 .. the_message_size - 1));
  @ requires \valid(the_digest + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
  @ requires \separated(the_message, the_digest);
  @ assigns the_digest[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
  @*/
void hmac(message the_message, size_t the_message_size, digest the_digest);

/*@ requires \valid_read(the_message + (0 .. the_message_size - 1));
  @ requires \valid(the_digest + (0 .. AES_BLOCK_LENGTH_BYTES - 1));
  @ requires \separated(the_message, the_digest);
  @ requires the_message_size % AES_BLOCK_LENGTH_BYTES == 0;
  @ assigns the_digest[0 .. AES_BLOCK_LENGTH_BYTES - 1];
  @*/
void aes_cbc_mac(message the_message, size_t the_message_size, block the_digest);

#endif
