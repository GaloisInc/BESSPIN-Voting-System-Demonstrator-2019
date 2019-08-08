#include "crypto_t.h"

void copy_base64_aes128_block (base64_aes128_block dst, // OUT
      	                       base64_aes128_block src) // IN
{
  /*@
    loop invariant 0 <= j <= BASE_64_AES_BLOCK_LENGTH_BYTES;
    loop invariant \forall integer k; 0 <= k < j ==> dst[k] == src[k];
    loop assigns j, dst[0 .. BASE_64_AES_BLOCK_LENGTH_BYTES - 1];
    loop variant BASE_64_AES_BLOCK_LENGTH_BYTES - j;
  */
  for (int j = 0; j < BASE_64_AES_BLOCK_LENGTH_BYTES; j++)
    {
      dst[j] = src[j];
    }
}

void copy_sha256_digest (sha256_digest dst, // OUT
                         sha256_digest src) // IN
{
  /*@
    loop invariant 0 <= j <= SHA256_DIGEST_LENGTH_BYTES;
    loop invariant \forall integer k; 0 <= k < j ==> dst[k] == src[k];
    loop assigns j, dst[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
    loop variant SHA256_DIGEST_LENGTH_BYTES - j;
  */
  for (int j = 0; j < SHA256_DIGEST_LENGTH_BYTES; j++)
    {
      dst[j] = src[j];
    }
}
