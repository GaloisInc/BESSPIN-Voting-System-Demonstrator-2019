/**
 * Smart Ballot Logging API
 * @refine log.lando
 */
#ifndef __LOG_H__
#define __LOG_H__

// General includes
#include <stdbool.h>
#include <stdint.h>

// Subsystem includes
#include "log_t.h"

// @design kiniry In this API should logs be referred to via filenames
// or file pointers?
log create_log(const log_name the_log_name);

void write_entry(const log the_log, const log_entry a_log_entry);

void export_log(const log the_log, log_io_stream a_target);

log import_log(const log the_log_name);

bool verify_well_formedness(const log the_log);

#endif /* __LOG_H__ */
