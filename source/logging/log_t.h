/**
 * Smart Ballot Logging Types
 * @refine log.lando
 */

#ifndef __LOG_T__
#define __LOG_T__

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define LOG_ENTRY_LENGTH 256

typedef char *log_name;

// These have moved to log_io.h - delete when build and analysis OK
//typedef Log_Handle *log;
//typedef FIL* log;
//typedef FIL* log_io_stream;

typedef uint8_t log_entry[LOG_ENTRY_LENGTH];

#endif
