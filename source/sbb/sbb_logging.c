/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_logging.h"

const log_name system_log_file_name = "system_log.txt";
const log_name app_log_file_name    = "application_log.txt";

void load_or_create(log_file *the_file, const log_name the_name) {
  if ( Log_IO_File_Exists(the_name) ) {
    *the_file = import_log(the_name);
    verify_log_well_formedness(*the_file);
    // @todo handle errors when this procedure is updated
  } else {
    create_log(the_file, the_name);
    // @todo handle errors when this procedure is updated
  }
}

void load_or_create_logs(void) {
  load_or_create(app_log_file, app_log_file_name);
  load_or_create(system_log_file, system_log_file_name);
}

void log_system_message(const log_entry new_entry) {
  write_entry(system_log_file, new_entry);
}
