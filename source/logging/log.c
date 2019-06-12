/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes
#include <string.h>

// Subsystem includes
#include "log.h"

log create_log(const log_name the_log_name) {
  return NULL;
}

void write_entry(const log the_log, const log_entry a_log_entry) {
  UINT n;
  FRESULT res = f_write (the_log,a_log_entry,LOG_ENTRY_LENGTH,&n);
  return;
}

bool verify_log_entry_well_formedness(const log_entry a_log_entry) {
  return false;
}

void export_log(const log the_log, log_io_stream a_target) {
  return;
}

log import_log(const log the_log_name) {
  return NULL;
}

bool verify_log_well_formedness(const log the_log) {
  return false;
}
