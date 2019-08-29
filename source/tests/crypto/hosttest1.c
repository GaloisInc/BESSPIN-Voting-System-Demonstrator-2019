// Test cases from NIST AES Algorithm Validation Suite
// See https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/aes/AESAVS.pdf

#include "aes.h"
#include "internal.h"
#include "modes.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define KEY_SIZE_BYTES 32

typedef unsigned char aes_block[AES_BLOCK_SIZE_BYTES];
typedef unsigned char key256[KEY_SIZE_BYTES];

void dump(aes_block b)
{
    for (int i = 0; i < AES_BLOCK_SIZE_BYTES; i++)
    {
        printf("%02x ", b[i]);
    }
    printf("\n");
}

int main()
{
    AES_KEY aes_ks1;

    printf("NIST AES Algorithm Validation Suite\n");
    printf("Section D.3\n");

    {
        key256 key = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block iv = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        AES_set_encrypt_key(key, 256, &aes_ks1);
        AES_cbc_encrypt(bufp, bufc, (size_t)16, &aes_ks1, iv, AES_ENCRYPT);
        dump(bufc);
    }

    {
        key256 key = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block iv = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0xc0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        AES_set_encrypt_key(key, 256, &aes_ks1);
        AES_cbc_encrypt(bufp, bufc, (size_t)16, &aes_ks1, iv, AES_ENCRYPT);
        dump(bufc);
    }

    {
        key256 key = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block iv = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};

        AES_set_encrypt_key(key, 256, &aes_ks1);
        AES_cbc_encrypt(bufp, bufc, (size_t)16, &aes_ks1, iv, AES_ENCRYPT);
        dump(bufc);
    }

    printf("Section E.3\n");

    {
        key256 key = {0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0,    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block iv = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        AES_set_encrypt_key(key, 256, &aes_ks1);
        AES_cbc_encrypt(bufp, bufc, (size_t)16, &aes_ks1, iv, AES_ENCRYPT);
        dump(bufc);
    }

    {
        key256 key = {0xc0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0,    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block iv = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        AES_set_encrypt_key(key, 256, &aes_ks1);
        AES_cbc_encrypt(bufp, bufc, (size_t)16, &aes_ks1, iv, AES_ENCRYPT);
        dump(bufc);
    }

    {
        key256 key = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};

        aes_block iv = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        AES_set_encrypt_key(key, 256, &aes_ks1);
        AES_cbc_encrypt(bufp, bufc, (size_t)16, &aes_ks1, iv, AES_ENCRYPT);
        dump(bufc);
    }

    return 0;
}
