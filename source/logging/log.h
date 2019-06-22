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
#include "log.acsl"
#include "log_io.h"
#include "log_t.h"

/*@ requires \valid(new_log_file);
  @ requires valid_string(the_log_name);
  @ requires \separated(new_log_file, the_log_name);
  @ assigns *new_log_file \from the_log_name, fs;
  @*/
void create_log(log_file new_log_file, const log_name the_log_name);

/*@ requires \valid(the_log);
  @ requires \valid_read(a_log_entry + (0 .. LOG_ENTRY_LENGTH - 1));
  @ requires \separated(the_log, a_log_entry);
  @ assigns  fs \from fs, the_log, a_log_entry;
  @*/
void write_entry(const log_file the_log, const log_entry a_log_entry);

/*@ requires \valid_read(a_log_entry + (0 .. LOG_ENTRY_LENGTH - 1));
  @ assigns  \result \from a_log_entry;
  @*/
bool verify_log_entry_well_formedness(const log_entry a_log_entry);

// @design kiniry I do not understand how these two functions are
// duals of each other, given that once you export a log to a device
// (which may be a socket, for all we know), there is no binding
// between that export and its `log_file`.  I *think* that
// `import_log` has to return a `Log_Handle`?

// @review kiniry I'm experiencing some type confusion as well between
// `log_name` and `log_file`.

// @todo re-evaluate frame axiom for this function.
/*@ requires \valid(the_log);
  @ requires \separated(the_log, a_target);
  @ assigns \nothing; // TBD
  @*/
void export_log(const log_file the_log, const log_io_stream a_target);

/*@ requires \valid(the_log_name);
  @ assigns  \result \from fs, the_log_name;
  @*/
log_file import_log(const log_name the_log_name);

/*@ requires \valid(the_log);
  @ assigns  \result \from fs, the_log;
  @*/
bool verify_log_well_formedness(const log_file the_log);

#endif /* __LOG_H__ */
