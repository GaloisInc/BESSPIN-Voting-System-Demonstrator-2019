#include "hsm.h"

void hmac (const aes256_key key,     // IN
	   const char       msg[],   // IN
	   const size_t     msg_size,       // IN
           sha256_digest    *const digest)  // OUT
{
  for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      *digest[i] = (uint8_t) i;
    }
}


void sha256 (const uint8_t msg[],     // IN
	     const size_t  msg_size,       // IN
             sha256_digest *const digest)  // OUT
{
  for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      *digest[i] = (uint8_t) (255 - i); // just for fun
    }
}
