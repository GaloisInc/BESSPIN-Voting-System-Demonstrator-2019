#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"


char *a_barcode       = "Not a good barcode at all, really shabby stuff";
char *another_barcode = "Also bad.";

int main(void) {
    assert(BARCODE_VALID != crypto_check_barcode_valid(a_barcode, strlen(a_barcode)));
    assert(BARCODE_VALID != crypto_check_barcode_valid(another_barcode, strlen(another_barcode)));

    return 0;
}
