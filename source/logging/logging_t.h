/**
 * Smart Ballot Logging Types
 * @refine sbb_security.lando
 */

#ifndef __LOGGING_T__
#define __LOGGING_T__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include "ff.h" /* Declarations of FatFs API */

#define LOG_ENTRY_LENGTH 256

typedef uint8_t log_entry[LOG_ENTRY_LENGTH];

#endif
