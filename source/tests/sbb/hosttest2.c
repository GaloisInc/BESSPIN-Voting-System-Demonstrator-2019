#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"

// One of the bytes has been changed
char *a_barcode =
    "2019+06+23+17+45:Dgep2UpFCE2XLgx6QZUfW3hlVhINicNbwL9KI8UtUGM=";

// The barcode has expired
char *another_barcode =
    "2019+05+26+18+13:BX99C4QSlcCUg5SIW1sfrPBufVmZl87db4xLu7lytQM=";

int main(void) {
    assert(BARCODE_VALID != crypto_check_barcode_valid(a_barcode, strlen(a_barcode)));
    assert(BARCODE_VALID != crypto_check_barcode_valid(another_barcode, strlen(another_barcode)));

    return 0;
}
