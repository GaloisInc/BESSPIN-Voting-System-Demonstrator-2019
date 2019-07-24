#ifndef __DEBUG_IO_H__
#define __DEBUG_IO_H__

#include <string.h>
#include <stdio.h>
#include <stdarg.h>

#include "log_io.h"

#ifdef LOG_SYSTEM_DEBUG
#define log_system_debug_printf debug_printf
#else
#define log_system_debug_printf(...)
#endif // LOG_SYSTEM_DEBUG

#define LOG_PORT_NUMBER 8066

/*@ assigns \nothing; // TBD
*/
int debug_printf(const char *the_format, ...);

/*@ requires \valid(the_io_stream);
  @ requires \valid(the_format);
  @ // requires \strlen(the_format) >= 0; // it's really a string
  @ assigns \nothing; // TBD
  @*/
int debug_log_printf(log_io_stream the_io_stream, const char *the_format, ...);

#endif // __DEBUG_IO_H__
