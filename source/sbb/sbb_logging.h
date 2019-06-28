/**
 * Smart Ballot Box Logging Definitions
 */
#ifndef __SBB_LOGGING_
#define __SBB_LOGGING_

#include "sbb_t.h"
#include "log.h"

// @design abakst these are handles to the app and system logs
extern Log_Handle app_log_handle;
extern Log_Handle system_log_handle;

extern const log_name system_log_file_name;
extern const log_name app_log_file_name;


// For now, overwite the existing log
// @todo check for errors once it is possible to do so
//@ requires true;
void load_or_create_logs(void);

//@ requires true;
void log_system_message(const log_entry new_entry);

#define CHANGE_STATE(_state, _field, _new_state)                        \
  do { _state._field = _new_state;                                      \
       const log_entry state_change_entry = "State change: " #_field " := " #_new_state; \
       log_system_message(state_change_entry); } while (0)
#endif
