#ifndef __SBB_CRYPTO__
#define __SBB_CRYPTO__
#include "sbb_t.h"

// This is defined in the cryptol specification
#define TIMESTAMP_LENGTH_BYTES 16
// These macros are dependent on the election parameters (No. of contests/candidates)
#define ENCRYPTED_BALLOT_LENGTH_BYTES (AES_BLOCK_LENGTH_BYTES)
// From formula in cryptol spec, 4 * ((8 * n) /^ 6 /^ 4)
// where n = ENCRYPTED_BALLOT_LENGTH_BYTES + AES_BLOCK_LENGTH_BYTES
#define BASE64_ENCODED_LENGTH 44
#define BASE64_DECODED_BYTES 32

/*@ assigns \nothing;
  @ ensures \result == true || \result == false;
 */
bool crypto_check_barcode_valid(barcode_t barcode, barcode_length_t length);

/*@ assigns \nothing;
  @ ensures \result == true || \result == false;
*/
bool timestamp_lte_now(const uint8_t *barcode_time);
#endif //__SBB_CRYPTO__
