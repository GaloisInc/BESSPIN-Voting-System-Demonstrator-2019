/**
 * Smart Ballot Box API
 * based on sbb.lando
 */
#include <stdbool.h>
#include <stdint.h>

/**
 * Perform Tally!
 * Uploads votes to some server?
 */
void perform_tally(void);

/**
 * Is barcode valid?
 * Check validity of the given barcode string
 */
bool is_barcode_valid(char * str, uint8_t len);
