#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"


/**
   key = join (repeat [0, 0xff]) : [32][8]
   iv  = repeat 0
   ballot = { time = 1234, contests = [1, 2] } : Ballot 2 2
*/
unsigned char *a_barcode =
    "0000001234:nCNC9iukz4Ne5uu5PM2En45SB7JB_QdzmMwIKF4EKS4=";

int main(void) {
    assert(crypto_check_barcode_valid(a_barcode, strlen(a_barcode)));
}
