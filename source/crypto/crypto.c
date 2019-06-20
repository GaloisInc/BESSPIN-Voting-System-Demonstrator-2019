/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

// General includes

// Subsystem includes
#include "crypto.h"

// All software implementation of AES. To be replaced when hardware HSM is available
#include "aes.h"

// All software implementation of SHA2. To be replaced when hardware HSM is available
#include "sha2-openbsd.h"

typedef unsigned char key256[AES256_KEY_LENGTH_BYTES];

// This is for initial integration and testing only
static const key256 mock_key =
  { 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff };

void encrypt(plaintext_block the_plaintext, ciphertext_block the_ciphertext)
{
  AES_KEY key_schedule;

  // Only fails if mock_key == NULL || &key_schedule == NULL
  AES_set_encrypt_key (mock_key, AES256_KEY_LENGTH_BITS, &key_schedule);
  AES_encrypt (the_plaintext, the_ciphertext, &key_schedule);
}

void decrypt(ciphertext_block the_ciphertext, plaintext_block the_plaintext)
{
  AES_KEY key_schedule;

  // Only fails if mock_key == NULL || &key_schedule == NULL
  AES_set_decrypt_key (mock_key, AES256_KEY_LENGTH_BITS, &key_schedule);
  AES_decrypt (the_ciphertext, the_plaintext, &key_schedule);
}

void hash(message the_message, size_t the_message_size, digest the_digest) {
  SHA2_CTX context;
  SHA256Init (&context);
  SHA256Update (&context, the_message, the_message_size);  
  SHA256Final (the_digest, &context);
}

void hmac(message the_message, size_t the_message_size, digest the_digest) {
  return;
}
