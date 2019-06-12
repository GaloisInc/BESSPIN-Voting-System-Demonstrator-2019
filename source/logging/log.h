/**
 * Smart Ballot Logging API
 * @refine log.lando
 */
#ifndef __LOG_H__
#define __LOG_H__

// General includes
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
// Subsystem includes
#include "log_t.h"
#include "log.acsl"

// @design kiniry In this API should logs be referred to via filenames
// or file pointers?
// @dragan log should be referred via file pointers

/*@
  @ requires valid_string(the_log_name);
@*/
log create_log(const log_name the_log_name);

/*@ requires \valid_read(a_log_entry + (0 .. LOG_ENTRY_LENGTH -1));
  @ requires \valid(the_log);
  @ requires \separated(the_log, a_log_entry);
@*/
void write_entry(const log the_log, const log_entry a_log_entry);

/*@
  @ requires \valid_read(a_log_entry + (0 .. LOG_ENTRY_LENGTH -1));
@*/
bool verify_log_entry_well_formedness(const log_entry a_log_entry);

void export_log(const log the_log, log_io_stream a_target);

/*@
  @ requires \valid(the_log_name);
@*/
log import_log(const log the_log_name);

bool verify_log_well_formedness(const log the_log);

#endif /* __LOG_H__ */
