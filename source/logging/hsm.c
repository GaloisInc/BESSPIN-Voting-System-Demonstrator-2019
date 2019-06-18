#include "hsm.h"
void hmac(const aes256_key key,      // IN
	  const message    msg,      // IN
	  const size_t     msg_size, // IN
          digest           the_digest)  // OUT
{
  for (uint8_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      the_digest[i] = i;
    }
}


void sha256(const message msg,         // IN
	    const size_t  msg_size,    // IN
            digest        the_digest)  // OUT
{
  for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      the_digest[i] = (uint8_t) (255 - i); // just for fun
    }
    
}
