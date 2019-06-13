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

#define AES256_KEY_LENGTH_BITS 256
#define AES256_KEY_LENGTH_BYTES (AES256_KEY_LENGTH_BITS / 8)
typedef uint8_t aes256_key[AES256_KEY_LENGTH_BYTES];

#define SHA256_DIGEST_LENGTH_BITS 256
#define SHA256_DIGEST_LENGTH_BYTES (SHA256_DIGEST_LENGTH_BITS / 8)
typedef uint8_t sha256_digest[SHA256_DIGEST_LENGTH_BYTES];

/*@
    requires \valid_read (key + (0 .. AES256_KEY_LENGTH_BYTES - 1));
    requires \valid_read (msg + (0 .. msg_size - 1));
    requires \separated (key, msg, digest);
    assigns \nothing;
    ensures  \valid (digest + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
*/
void hmac (const aes256_key key,     // IN
	   const char       msg[],   // IN
	   const size_t     msg_size,       // IN
           uint8_t          *const digest); // OUT

/*@
    requires \valid_read (msg + (0 .. msg_size - 1));
    requires \separated (msg, digest);
    assigns \nothing;
    ensures  \valid (digest + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
*/
void sha256 (const uint8_t msg[],     // IN
	     const size_t  msg_size,       // IN
             sha256_digest *const digest); // OUT

#endif
