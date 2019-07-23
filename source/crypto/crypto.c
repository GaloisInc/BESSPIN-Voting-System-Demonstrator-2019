/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

// General includes
#ifndef TARGET_OS_FreeRTOS
// assert.h not supported on RISCV/FreeRTOS
#include <assert.h>
#endif

// Subsystem includes
#include "crypto.h"

// All software implementation of AES. To be replaced when hardware HSM is available
#include "aes.h"

// All software implementation of SHA2. To be replaced when hardware HSM is available
#include "sha2-openbsd.h"

typedef uint8_t key256[AES256_KEY_LENGTH_BYTES];

// This is for initial integration and testing only
static const key256 mock_key = "From Russia with Love";

void aes_encrypt(plaintext_block the_plaintext, ciphertext_block the_ciphertext)
{
    AES_KEY key_schedule;

    // Only fails if mock_key == NULL || &key_schedule == NULL
    AES_set_encrypt_key(mock_key, AES256_KEY_LENGTH_BITS, &key_schedule);
    AES_encrypt(the_plaintext, the_ciphertext, &key_schedule);
}

void aes_decrypt(ciphertext_block the_ciphertext, plaintext_block the_plaintext)
{
    AES_KEY key_schedule;

    // Only fails if mock_key == NULL || &key_schedule == NULL
    AES_set_decrypt_key(mock_key, AES256_KEY_LENGTH_BITS, &key_schedule);
    AES_decrypt(the_ciphertext, the_plaintext, &key_schedule);
}

void hash(message the_message, size_t the_message_size, digest the_digest)
{
    SHA2_CTX context;
    SHA256Init(&context);
    SHA256Update(&context, the_message, the_message_size);
    SHA256Final(the_digest, &context);
}

void hmac(message the_message, size_t the_message_size, digest the_digest)
{

    ///////////////////////////////////////////////////
    // NOTE - This is a "mock" implementation        //
    // It does not implement the true HMAC algorithm //
    // but rather implements something simpler that  //
    // exhibits the properties of a MAC function     //
    // without the cryptographic provenance of HMAC  //
    //                                               //
    // This implementation is only intended as a     //
    // placeholder to allow the integration and test //
    // of other subsystem on which it depends to     //
    // progress                                      //
    ///////////////////////////////////////////////////

    // This is NOT the proper HMAC Algorithm
    SHA2_CTX context;
    SHA256Init(&context);

    // Mix in the mock_key
    SHA256Update(&context, mock_key, AES256_KEY_LENGTH_BYTES);

    // Plus the_message itself
    SHA256Update(&context, the_message, the_message_size);

    SHA256Final(the_digest, &context);
}

void aes_cbc_mac(message the_message, size_t the_message_size, block the_digest)
{
    AES_KEY key_schedule;
    size_t block_count;
    uint8_t *current_data_ptr = the_message;
    aes128_block iv = {0};
    aes128_block plaintext_block = {0};
    aes128_block ciphertext_block = {0};

#ifndef TARGET_OS_FreeRTOS
    assert(the_message_size % AES_BLOCK_LENGTH_BYTES == 0);
#endif

    // Only fails if mock_key == NULL || &key_schedule == NULL
    AES_set_encrypt_key(mock_key, AES256_KEY_LENGTH_BITS, &key_schedule);

    block_count = the_message_size / AES_BLOCK_LENGTH_BYTES;

    // For each block of input data
    for (size_t b = 0; b < block_count; b++)
    {
        // Input data to encrypt is IV xor Mi
        for (size_t i = 0; i < AES_BLOCK_LENGTH_BYTES; i++)
        {
            plaintext_block[i] = iv[i] ^ (*current_data_ptr);
            current_data_ptr++;
        }
        AES_encrypt(plaintext_block, ciphertext_block, &key_schedule);

        // Copy the newly encrypted block back into IV for the next time.
        for (size_t j = 0; j < AES_BLOCK_LENGTH_BYTES; j++)
        {
            iv[j] = ciphertext_block[j];
        }
    }

    // When the loop terminates, the final MAC value is the result of the final
    // encryption, which is now in both ciphertext_block and iv
    for (size_t i = 0; i < AES_BLOCK_LENGTH_BYTES; i++)
    {
        the_digest[i] = iv[i];
    }
}
