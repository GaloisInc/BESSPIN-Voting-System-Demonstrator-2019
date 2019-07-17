#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"


unsigned char *a_barcode =
    "2019:07:16:18:13:AX99C4QSlcCUg5SIW1sfrApDW9K-Hcq2c1mgBBq3Vf0=";

int main(void) {
    assert(!crypto_check_barcode_valid(a_barcode, strlen(a_barcode)));

    return 0;
}
