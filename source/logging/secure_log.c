/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes

// Subsystem includes
#include "secure_log.h"

void write_entry_to_secure_log(const secure_log the_secure_log,
                               const log_entry a_log_entry) {
  // @example kiniry I wrote this example sketch implementation while
  // talking to Dragan about type refinement in C and the relationship
  // between the features of secure log and log.
  // write_entry(the_secure_log, a_log_entry);
  // digest d = hash(the_last_digest, a_log_entry);
  // write(d, the_secure_log);
}

