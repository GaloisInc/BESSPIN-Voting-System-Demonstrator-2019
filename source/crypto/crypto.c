/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

// General includes
#include "votingdefs.h"

// Subsystem includes
#include "crypto/crypto.h"

// All software implementation of AES. To be replaced when hardware HSM is available
#include "crypto/aes.h"

// All software implementation of SHA2. To be replaced when hardware HSM is available
#include "crypto/sha2-openbsd.h"

// the mock/default key, used for testing and returned when an unknown
// key is asked for
static const aes256_key mock_key = "From Russia with Love";

// Local function declarations

// Returns a pointer to the key data for the given Key Name
const uint8_t *fetch_key (AES_Key_Name key);

// Local function bodies

const uint8_t *fetch_key (AES_Key_Name key)
{
  // The body of this function is implemented differently on FreeRTOS and POSIX

#ifdef TARGET_OS_FreeRTOS
    const uint8_t *result;
    
    // we simply return addresses of the hard-coded keys that were linked
    // in at compile time, with the mock key returned in any situation
    // where one of the 3 "real" keys is not asked for
    switch (key) {
    case Barcode_MAC_Key:
        result = &barcode_mac_key[0];
        break;
    
    case Log_Root_Block_MAC_Key:
        result = &log_root_block_mac_key[0];
        break;
        
    case Log_Entry_MAC_Key:
        result = &log_entry_mac_key[0];
        break;
        
    default:
        result = &mock_key[0];
        break;
    }

    return result;
#else // POSIX systems

  // For host testing, we return the same mock key for all cases
  return mock_key;

#endif // TARGET_OS_FreeRTOS
}

// Export function bodies

void aes_encrypt(plaintext_block the_plaintext, ciphertext_block the_ciphertext, AES_Key_Name key)
{
    AES_KEY key_schedule;

    // Only fails if fetch_key (key) == NULL || &key_schedule == NULL
    AES_set_encrypt_key(fetch_key (key), AES256_KEY_LENGTH_BITS, &key_schedule);
    AES_encrypt(the_plaintext, the_ciphertext, &key_schedule);
}

void aes_decrypt(ciphertext_block the_ciphertext, plaintext_block the_plaintext, AES_Key_Name key)
{
    AES_KEY key_schedule;

    // Only fails if fetch_key (key) == NULL || &key_schedule == NULL
    AES_set_decrypt_key(fetch_key (key), AES256_KEY_LENGTH_BITS, &key_schedule);
    AES_decrypt(the_ciphertext, the_plaintext, &key_schedule);
}

void hash(message the_message, size_t the_message_size, digest the_digest)
{
    SHA2_CTX context;
    SHA256Init(&context);
    SHA256Update(&context, the_message, the_message_size);
    SHA256Final(the_digest, &context);
}


void aes_cbc_mac(message the_message, size_t the_message_size,
                 block the_digest, AES_Key_Name key)
{
    AES_KEY key_schedule;
    size_t block_count;
    uint8_t *current_data_ptr = the_message;
    aes128_block iv = {0};
    aes128_block local_plaintext_block = {0};
    aes128_block local_ciphertext_block = {0};

    osd_assert(the_message_size % AES_BLOCK_LENGTH_BYTES == 0);

    // Only fails if mock_key == NULL || &key_schedule == NULL
    AES_set_encrypt_key(fetch_key (key), AES256_KEY_LENGTH_BITS, &key_schedule);

    block_count = the_message_size / AES_BLOCK_LENGTH_BYTES;

    // For each block of input data
    /*@
      loop invariant 0 <= b <= block_count;
      loop assigns b, current_data_ptr,
                   local_plaintext_block[0 .. AES_BLOCK_LENGTH_BYTES - 1];
      loop variant block_count - b;
    */
    for (size_t b = 0; b < block_count; b++)
    {
        // Input data to encrypt is IV xor Mi
	/*@
	  loop invariant 0 <= i <= AES_BLOCK_LENGTH_BYTES;
	  loop assigns i,
                       current_data_ptr,
                       local_plaintext_block[0 .. AES_BLOCK_LENGTH_BYTES - 1],
                       iv[0 .. AES_BLOCK_LENGTH_BYTES - 1];
          loop variant AES_BLOCK_LENGTH_BYTES - i;
	*/
        for (size_t i = 0; i < AES_BLOCK_LENGTH_BYTES; i++)
        {
            local_plaintext_block[i] = iv[i] ^ (*current_data_ptr);
            current_data_ptr++;
        }
        AES_encrypt(local_plaintext_block, local_ciphertext_block, &key_schedule);

        // Copy the newly encrypted block back into IV for the next time.
	/*@
	  loop invariant 0 <= j <= AES_BLOCK_LENGTH_BYTES;
	  loop assigns j, iv[0 .. AES_BLOCK_LENGTH_BYTES - 1];
	  loop variant AES_BLOCK_LENGTH_BYTES - j;
	*/
        for (size_t j = 0; j < AES_BLOCK_LENGTH_BYTES; j++)
        {
            iv[j] = local_ciphertext_block[j];
        }
    }

    // When the loop terminates, the final MAC value is the result of the final
    // encryption, which is now in both ciphertext_block and iv
    /*@
      loop invariant 0 <= i <= AES_BLOCK_LENGTH_BYTES;
      loop assigns i, the_digest[0 .. AES_BLOCK_LENGTH_BYTES - 1];
      loop variant AES_BLOCK_LENGTH_BYTES - i;
    */
    for (size_t i = 0; i < AES_BLOCK_LENGTH_BYTES; i++)
    {
        the_digest[i] = iv[i];
    }
}
