#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"


unsigned char *a_barcode       = "Not a good barcode at all, really shabby stuff";
unsigned char *another_barcode = "Also bad.";

int main(void) {
    assert(!crypto_check_barcode_valid(a_barcode, strlen(a_barcode)));
    assert(!crypto_check_barcode_valid(another_barcode, strlen(another_barcode)));

    return 0;
}
