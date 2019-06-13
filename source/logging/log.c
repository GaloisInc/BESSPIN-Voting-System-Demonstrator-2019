/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes
#include <string.h>

// Subsystem includes
#include "log.h"
#include "secure_log.h"

void create_log(Log_Handle *log,
		const log_name the_log_name)
{
  const log_entry first_entry = "hello worldxxxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

  const secure_log_security_policy first_policy = { hashchain_sha2_256,
						    no_provenance,
						    no_confidentiality,
						    hmac_sha2_256,
						    no_access_control,
						    no_non_repudiation };
						     
  create_secure_log (log, the_log_name, first_entry, first_policy);
}

void write_entry(const log the_log, const log_entry a_log_entry) {
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
