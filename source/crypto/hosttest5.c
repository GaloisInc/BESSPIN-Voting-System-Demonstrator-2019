// HostTest Case 5
// Tests for AES-CBC MAC

#include "aes.h"
#include "internal.h"
#include "modes.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "crypto.h"

#define KEY_SIZE_BYTES 32

typedef uint8_t two_blocks[32];
typedef uint8_t three_blocks[48];

typedef uint8_t key256[KEY_SIZE_BYTES];

// Same key as mock_key in crypto.c
key256 testkey = {0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
                  0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
                  0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
                  0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff};

void dump(aes128_block b)
{
    for (int i = 0; i < AES_BLOCK_SIZE_BYTES; i++)
    {
        printf("%02x ", b[i]);
    }
    printf("\n");
}

// TEST CASES FOR AES-CBC-MAC
//
// Results of these test cases are printed to stdout.
//
// These have been checked manually against the results obtained using
// the on-line implemenation at:
//   http://www.cryptogrium.com/aes-cbc.html
// with the same Key, IV and input data.

int main()
{
    {
        aes128_block bufp = {0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes128_block mac = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        // MAC with input data 1 block
        printf("Test case 1\n");
        aes_cbc_mac(bufp, 16, mac, Barcode_MAC_Key);
        dump(mac);
    }

    {
        two_blocks bufp = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                           0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                           0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
                           0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55};

        aes128_block mac = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        // MAC with input data 2 blocks
        printf("Test case 2\n");
        aes_cbc_mac(bufp, 32, mac, Barcode_MAC_Key);
        dump(mac);
    }
    {
        three_blocks bufp = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                             0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
                             0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
                             0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
                             0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55};

        aes128_block mac = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        // MAC with input data 3 blocks
        printf("Test case 3\n");
        aes_cbc_mac(bufp, 48, mac, Barcode_MAC_Key);
        dump(mac);
    }

    {
        aes128_block bufp = {0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
        aes128_block mac = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

        // MAC with input data 1 block, but wrong size
        printf("Test case 4 - wrong size - expect assertion failure\n");
        aes_cbc_mac(bufp, 17, mac, Barcode_MAC_Key);
        dump(mac);
    }

    return 0;
}
