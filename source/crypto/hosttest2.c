// HostTest Case 2
// Compares results using same key and plaintext, but
// 1. Using aes.h directly,
// 2. Calling AES via crypto.h

#include "aes.h"
#include "internal.h"
#include "modes.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "crypto.h"

#define KEY_SIZE_BYTES 32

typedef unsigned char aes_block[AES_BLOCK_SIZE_BYTES];
typedef unsigned char key256[KEY_SIZE_BYTES];

// Same key as mock_key in crypto.c
key256 testkey = {0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
                  0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
                  0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
                  0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff};

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

    {
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp2 = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                           0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};

        printf("Encrypt with aes.h\n");
        AES_set_encrypt_key(testkey, 256, &aes_ks1);
        AES_encrypt(bufp, bufc, &aes_ks1);
        dump(bufc);

        printf("Decrypt with aes.h\n");
        AES_set_decrypt_key(testkey, 256, &aes_ks1);
        AES_decrypt(bufc, bufp2, &aes_ks1);
        dump(bufp2);
    }

    {
        aes_block bufc = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp = {0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes_block bufp2 = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                           0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};

        printf("Encrypt with crypto.h\n");
        aes_encrypt(bufp, bufc);
        dump(bufc);

        printf("Decrypt with crypto.h\n");
        aes_decrypt(bufc, bufp2);
        dump(bufp2);
    }
    return 0;
}
