/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

// General includes
#include <assert.h>

// Subsystem includes
#include "crypto.h"

// constant declarations for the crypto subsystem
const uint32_t AES_BLOCK_SIZE  = 256;
const uint32_t AES_KEY_SIZE    = 256;
const uint32_t SHA_DIGEST_SIZE = 256;

void encrypt(plaintext_block the_plaintext, ciphertext_block the_ciphertext) {
  assert(false);
  //@ assert false;
  return;
}

void decrypt(ciphertext_block the_ciphertext, plaintext_block the_plaintext) {
  assert(false);
  //@ assert false;
  return;
}

void hash(message the_message, uint32_t the_message_size, digest the_digest) {
  assert(false);
  //@ assert false;
  return;
}

void hmac(message the_message, uint32_t the_message_size, digest the_digest) {
  assert(false);
  //@ assert false;
  return;
}
