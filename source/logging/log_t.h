/**
 * Smart Ballot Logging Types
 * @refine log.lando
 */

#ifndef __LOG_T__
#define __LOG_T__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <ff.h>

#define LOG_ENTRY_LENGTH 256

typedef char* log_name;
typedef FIL* log;
typedef FIL* log_io_stream;
typedef char log_entry[LOG_ENTRY_LENGTH];

#endif
