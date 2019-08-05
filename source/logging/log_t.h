/**
 * Smart Ballot Logging Types
 * @refine log.lando
 */

#ifndef __LOG_T__
#define __LOG_T__

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "../crypto/crypto_t.h"

typedef char* log_name;

#define LOG_ENTRY_LENGTH 256
typedef uint8_t log_entry[LOG_ENTRY_LENGTH];

// Whole array assignment of src[0.. LOG_ENTRY_LENGTH - 1] to dst[0 .. LOG_ENTRY_LENGTH - 1]

/*@ requires \valid(dst + (0 .. LOG_ENTRY_LENGTH - 1));
    requires \valid_read(src + (0 .. LOG_ENTRY_LENGTH - 1));
    requires \separated(dst + (0 .. LOG_ENTRY_LENGTH - 1), src + (0 .. LOG_ENTRY_LENGTH - 1));
    assigns dst[0 .. LOG_ENTRY_LENGTH - 1];
    ensures \forall integer i; 0 <= i < LOG_ENTRY_LENGTH ==> dst[i] == src[i];
*/
void copy_log_entry (log_entry dst,  // OUT
		     log_entry src); // IN

#endif
