/**
 * Smart Ballot Box API
 * based on sbb.lando
 */

#include "sbb.h"
#include <stdio.h>

void perform_tally(void)
{
    printf("Perorming tally\r\n");
}

bool is_barcode_valid(char * str, uint8_t len)
{
    (void) str;
    (void) len;
    return true;
}