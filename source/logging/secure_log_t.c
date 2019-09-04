#include "logging/secure_log_t.h"

void copy_sha256_base64_digest (sha256_base64_digest dst,       // OUT
                                const sha256_base64_digest src) // IN
{
  /*@
    loop invariant 0 <= j <= SHA256_BASE_64_DIGEST_LENGTH_BYTES;
    loop invariant \forall integer k; 0 <= k < j ==> dst[k] == src[k];
    loop assigns j, dst[0 .. SHA256_BASE_64_DIGEST_LENGTH_BYTES - 1];
    loop variant SHA256_BASE_64_DIGEST_LENGTH_BYTES - j;
  */
  for (int j = 0; j < SHA256_BASE_64_DIGEST_LENGTH_BYTES; j++)
    {
      dst[j] = src[j];
    }
}
