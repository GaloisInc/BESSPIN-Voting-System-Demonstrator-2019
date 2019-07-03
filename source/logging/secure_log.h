/**
 * Smart Ballot Logging API
 * @refine log.lando
 */
#ifndef __SECURE_LOG__
#define __SECURE_LOG__

// General includes

// Subsystem includes
#include "log.h"
#include "secure_log.acsl"
#include "secure_log_t.h"

typedef log_name secure_log_name;
typedef log_file secure_log;
typedef log_io_stream secure_log_io_stream;

// @spec kiniry These functions need ACSL specifications, based upon
// an axiomatic spec of logs in `secure_log.acsl` that algebraically
// matches that which was specified by Joey in Cryptol.

// @design kiniry We should probably write `the_policy` into the log's
// root block and authenticate it or, more likely, its first block
// after the authenticated zeroed root block.

/*@ requires \valid(secure_log);
  @ requires \valid_read(a_log_entry_type + (0 .. LOG_ENTRY_LENGTH - 1));
  @ assigns *secure_log \from fs, the_secure_log_name, a_log_entry_type, the_policy;
  @ ensures File_Is_Open (secure_log);
  @ ensures \valid(secure_log);
  @*/
void create_secure_log(Log_Handle *secure_log,
                       const secure_log_name the_secure_log_name,
                       const log_entry a_log_entry_type,
                       const secure_log_security_policy the_policy);

// TBD and Unimplemented at present
// /*@ requires \valid_read(((char*)a_secure_log_name) + (0 .. LOG_ENTRY_LENGTH -1));
//   @*/
// secure_log_entry secure_log_entry_kind(const secure_log_name a_secure_log_name);

/*@ requires \valid_read(a_log_entry + (0 .. LOG_ENTRY_LENGTH - 1));
  @ requires \valid(the_secure_log);
  @ requires \separated(the_secure_log, a_log_entry);
  @ assigns fs \from fs, the_secure_log, a_log_entry;
  @ ensures File_Is_Open (the_secure_log);
  @ ensures \valid(the_secure_log);
  @*/
void write_entry_to_secure_log(const secure_log the_secure_log,
                               const log_entry a_log_entry);

// TBD and Unimplemented at present
// /*@ requires \valid_read(the_secure_log_entry.the_entry  + (0 .. LOG_ENTRY_LENGTH - 1));
//   @ requires \valid_read(the_secure_log_entry.the_digest + (0 .. SHA256_DIGEST_LENGTH_BYTES - 1));
//   @*/
// bool verify_secure_log_entry_security(const secure_log_entry the_secure_log_entry);

/*@ requires \valid_read(the_secure_log);
  @ assigns \result \from fs, the_secure_log;
  @
  @ behavior failure:
  @ assumes File_Num_Entries(the_secure_log) ==0;
  @ assigns \nothing;
  @ ensures !\result;
  @
  @ behavior success:
  @ assumes File_Num_Entries(the_secure_log)>=1; 
  @ ensures \result;
  @
  @ complete behaviors failure, success;
  @ disjoint behaviors failure, success;
  @*/
bool verify_secure_log_security(secure_log the_secure_log);

#endif /* __SECURE_LOG__ */
