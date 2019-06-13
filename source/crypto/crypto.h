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
#include "crypto_t.h"
#include "crypto.acsl"

/*@ requires \valid(the_plaintext);
  @ requires \valid(the_ciphertext+(0..AES_BLOCK_SIZE-1));
  @ assigns the_ciphertext[0..AES_BLOCK_SIZE-1];
  @*/
void encrypt(plaintext_block the_plaintext, ciphertext_block the_ciphertext);

/*@ requires \valid(the_ciphertext);
  @ requires \valid(the_plaintext+(0..AES_BLOCK_SIZE-1));
  @ assigns the_plaintext[0..AES_BLOCK_SIZE-1];
  @*/
void decrypt(ciphertext_block the_ciphertext, plaintext_block the_plaintext);

/*@ requires \valid(the_message + (0..the_message_size));
  @ requires \valid(the_digest + (0..SHA_DIGEST_SIZE-1));
  @ assigns the_digest[0..SHA_DIGEST_SIZE-1];
  @*/
void hash(message the_message, uint32_t the_message_size, digest the_digest);

/*@ requires \valid(the_message + (0..the_message_size));
  @ requires \valid(the_digest + (0..SHA_DIGEST_SIZE-1));
  @ assigns the_digest[0..SHA_DIGEST_SIZE-1];
  @*/
void hmac(message the_message, uint32_t the_message_size, digest the_digest);

#endif
