// Test cases for basic SHA2-256
// See 

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
  // of running this Ada program, compiled with GNAT Community Edition 2018
  
  /* with GNAT.SHA256; use GNAT.SHA256; */
  /* with Ada.Text_IO; use Ada.Text_IO; */
  /* procedure Main2 */
  /* is */
  /*    C1 : constant String(1..32) := (others => 'A'); */
  /*    C2 : constant String(1..32) := (others => 'B'); */
  /*    C3 : constant String(1..32) := (others => 'C'); */
  /* begin */
  /*    Put_Line (Digest (C1)); */
  /*    Put_Line (Digest (C2)); */
  /*    Put_Line (Digest (C3)); */
  /* end Main2; */

  printf("SHA2-256 test vectors\n");
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
