/**
 * Smart Ballot Box Logging Definitions
 */
#include "sbb_t.h"
#include "log.h"

// @design abakst these are handles to the app and system logs
extern log_file app_log_file;
extern log_file system_log_file;

#define CHANGE_STATE(_state, _field, _new_state)                        \
  do { _state._field = _new_state;                                      \
       log_system_message("State change: " #_field " := " #_new_state) } while (0)


// For now, overwite the existing log
// @todo check for errors once it is possible to do so
void load_or_create_logs();

void log_system_message(const log_entry new_entry) {
  write_entry(system_log_file, new_entry);
}
