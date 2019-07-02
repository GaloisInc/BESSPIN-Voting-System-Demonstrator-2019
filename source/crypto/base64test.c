#include "base64.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main()
{
    unsigned char src[33]="dependingonwhethertheobjectpoint";
    unsigned char dst[46];
    unsigned char from_encoded_dst[33];
    unsigned char src_encoded[45]="ZGVwZW5kaW5nb253aGV0aGVydGhlb2JqZWN0cG9pbnQ=";
    size_t olen;
    size_t olen1;
    int r;

    printf("%s\n", "Test that 32 bytes become 44 bytes when Base64 encoded");

    r = mbedtls_base64_encode (dst, 0, &olen, src, 32);
    printf("required encoder dlen=%zu\n", olen);


    r = mbedtls_base64_encode (dst, 46, &olen, src, 32);
    printf("Encoded:%s\n", dst);
    printf("actual encoder olen=%zu\n", olen);

    r = mbedtls_base64_decode (NULL,0, &olen1, src_encoded, 44);
    printf("required decoder dlen=%zu\n", olen1);

    r = mbedtls_base64_decode (from_encoded_dst,33, &olen1, src_encoded, 44);

    printf("actual decode olen=%zu\n", olen);
    printf("r=%d\n", r);
    if ( r == 0) {
        printf("%s\n", "Success!");
    }else {
        printf("%s\n", "Failed." );
    }

    return 0;
}
