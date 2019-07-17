#ifndef __SBB_CRYPTO__
#define __SBB_CRYPTO__
#include "sbb_t.h"


/*@
  @ assigns \nothing;
  @ ensures \result == true || \result == false;
 */
bool crypto_check_barcode_valid(barcode_t barcode, barcode_length_t length);
#endif //__SBB_CRYPTO__
