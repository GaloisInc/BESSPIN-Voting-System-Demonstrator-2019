/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes
#include <stdio.h>
#include <string.h>

// Subsystem includes
#include "secure_log.h"

void write_entry_to_secure_log(const secure_log the_secure_log,
                               const log_entry a_log_entry) {
  write_entry(the_secure_log, a_log_entry);
  digest d = hash(the_last_digest, a_log_entry);
  write(d, the_secure_log);
}

