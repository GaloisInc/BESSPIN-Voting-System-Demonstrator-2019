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
#include "log_net_t.h"
#include "log_t.h"

/*@
  predicate
    Log_Is_Wellformed{L}(log_file f) = \true; // abstract
*/


/*@ requires \valid(new_log_file);
  @ requires valid_string(the_log_name);
  @ requires \separated(new_log_file, the_log_name);
  @ assigns *new_log_file \from the_log_name, log_fs, endpoint;
  @*/
Log_FS_Result create_log(log_file new_log_file,
                         const log_name the_log_name,
                         const http_endpoint endpoint);

/*@ requires \valid(the_log);
  @ requires \valid_read(a_log_entry + (0 .. LOG_ENTRY_LENGTH - 1));
  @ requires \separated(the_log, a_log_entry);
  @ assigns  log_fs \from log_fs, the_log, a_log_entry;
  @*/
Log_FS_Result write_entry(const log_file the_log, const log_entry a_log_entry);

/*@ requires \valid_read(a_log_entry + (0 .. LOG_ENTRY_LENGTH - 1));
  @ assigns  \result \from a_log_entry;
  @ ensures \result == false || \result == true;
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


/*@ requires \valid(the_log);
  @ assigns  \result \from log_fs, the_log;
  @ ensures  \result <==> Log_Is_Wellformed (the_log);
  @ ensures  \result == false || \result == true;
  @*/
bool verify_log_well_formedness(log_file the_log);



/*@ requires \valid(the_log_file);
  @ requires File_Is_Open (the_log_file);
  @
  @ assigns *the_log_file \from log_fs;
  @
  @ behavior log_ok:
  @   assumes Log_Is_Wellformed (the_log_file);
  @   ensures \result == true;
  @   ensures \valid (the_log_file);
  @   ensures File_Is_Open (the_log_file);
  @
  @ behavior log_bad:
  @   assumes !Log_Is_Wellformed (the_log_file);
  @   ensures \result == false;
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
bool import_log(log_file the_log_file);

#endif /* __LOG_H__ */
