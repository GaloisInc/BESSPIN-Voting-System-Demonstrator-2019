#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"


unsigned char *a_barcode =
    "2019+06+23+17+45:Dgep2UpFCE2XLgx6QZUfW3hlVhINicNbwL9KI8UtUGM=";

int main(void) {
    assert(!crypto_check_barcode_valid(a_barcode, strlen(a_barcode)));

    return 0;
}
