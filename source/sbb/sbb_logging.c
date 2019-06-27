/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_logging.h"

const log_name system_log_file_name = "system_log.txt";
const log_name app_log_file_name    = "application_log.txt";

void load_or_create_logs(void) {
  create_log(app_log_file, app_log_file_name);
  create_log(system_log_file, system_log_file_name);
}

void log_system_message(const log_entry new_entry) {
  write_entry(system_log_file, new_entry);
}
