#include "base64.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test1()
{
    unsigned char src[33]="dependingonwhethertheobjectpoint";
    unsigned char dst[46];
    unsigned char from_encoded_dst[33];
    unsigned char src_encoded[45]="ZGVwZW5kaW5nb253aGV0aGVydGhlb2JqZWN0cG9pbnQ=";
    size_t olen;
    size_t olen1;
    int r;

    printf("%s\n", "Test1 - Test that 32 bytes become 44 bytes when Base64 encoded");

    r = mbedtls_base64_encode (dst, 0, &olen, src, 32, false);
    printf("required encoder dlen=%zu\n", olen);


    r = mbedtls_base64_encode (dst, 46, &olen, src, 32, false);
    printf("Encoded:%s\n", dst);
    printf("actual encoder olen=%zu\n", olen);

    r = mbedtls_base64_decode (NULL,0, &olen1, src_encoded, 44);
    printf("required decoder dlen=%zu\n", olen1);

    r = mbedtls_base64_decode (from_encoded_dst, 33, &olen1, src_encoded, 44);

    printf("actual decode olen=%zu\n", olen1);
    printf("r=%d\n", r);
    if ( r == 0) {
        printf("%s\n", "Success!");
    } else {
        printf("%s\n", "Failed." );
    }
}

void test2()
{
  unsigned char src[3]= { 0xfb, 0xff, 0xbf };
  unsigned char dst[6];
  unsigned char encoded_ok[5]  = "-_-_"; // RFC 4648 - should be OK
  unsigned char encoded_bad[5] = "+/+/"; // not OK
  unsigned char decoded[3] = {0};

  size_t olen;
  int r;

  printf("Test2 - filename safe encoding of chars 62 and 63\n");

  r = mbedtls_base64_encode (dst, 6, &olen, src, 3, false);
  printf("Result=%d\n", r);
  printf("Encoded len=%zu\n", olen);
  printf("Encoded:%s\n\n", dst);

  r = mbedtls_base64_decode (decoded, 3, &olen, encoded_bad, 4);
  printf("Decode test - Bad input - Result=%d\n", r);
  if (r == 0)
    {
      printf("Decoded len=%zu\n", olen);
      printf("Decoded:%2X %2X %2X\n", decoded[0], decoded[1], decoded[2]);
    }

  r = mbedtls_base64_decode (decoded, 3, &olen, encoded_ok, 4);
  printf("Decode test - Ok input - Result=%d\n", r);
  if (r == 0)
    {
      printf("Decoded len=%zu\n", olen);
      printf("Decoded:%2X %2X %2X\n", decoded[0], decoded[1], decoded[2]);
    }


}

int main(void)
{
  test1();
  test2();
  return 0;

}
