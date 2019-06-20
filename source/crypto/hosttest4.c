// Test cases for basic HMAC-SHA256

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "crypto.h"

typedef uint8_t testdata[32];

void dump (sha_digest b)
{
  for (int i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
      printf ("%02x ", b[i]);
    }
  printf ("\n");
}

int main()
{
  // Results of this program have been compared against the results
  // of running hmac_oracle.adb, compiled with GNAT Community Edition 2018
  
  printf("HMAC-SHA256 test vectors (MOCK IMPLEMENTATION)\n");
  {
    // 32 'A' chars
    testdata m = { 65, 65, 65, 65, 65, 65, 65, 65,
		   65, 65, 65, 65, 65, 65, 65, 65,
		   65, 65, 65, 65, 65, 65, 65, 65,
		   65, 65, 65, 65, 65, 65, 65, 65 }; 
    sha_digest d;

    hash (m, 32, d);
    dump (d);
  }

  {
    // 32 'B' chars
    testdata m = { 66, 66, 66, 66, 66, 66, 66, 66,
		   66, 66, 66, 66, 66, 66, 66, 66,
		   66, 66, 66, 66, 66, 66, 66, 66,
		   66, 66, 66, 66, 66, 66, 66, 66 }; 
    sha_digest d;

    hash (m, 32, d);
    dump (d);
  }

  {
    // 32 'C' chars
    testdata m = { 67, 67, 67, 67, 67, 67, 67, 67,
		   67, 67, 67, 67, 67, 67, 67, 67,
		   67, 67, 67, 67, 67, 67, 67, 67,
		   67, 67, 67, 67, 67, 67, 67, 67 }; 
    sha_digest d;

    hash (m, 32, d);
    dump (d);
  }

  return 0;
}
