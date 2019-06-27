/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_logging.h"

void load_or_create_logs(); {
  create_log(app_log_file, app_log_file_name);
  create_log(system_log_file, system_log_file_name);
}
