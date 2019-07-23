/**
 * Smart Ballot Box Logging Definitions
 */
#ifndef __SBB_LOGGING_
#define __SBB_LOGGING_

#include "sbb_t.h"
#include "log.h"
#include "debug_io.h"

extern SBB_state the_state;

// @design abakst these are handles to the app and system logs
extern Log_Handle app_log_handle;
extern Log_Handle system_log_handle;

extern const log_name system_log_file_name;
extern const log_name app_log_file_name;

// HW event messages
extern const char *sensor_in_pressed_msg;
extern const char *sensor_in_released_msg;
extern const char *sensor_out_pressed_msg;
extern const char *sensor_out_released_msg;
extern const char *cast_button_pressed_msg;
extern const char *cast_button_released_msg;
extern const char *spoil_button_pressed_msg;
extern const char *spoil_button_released_msg;
extern const char *barcode_scanned_msg;
extern const char *barcode_received_event_msg;
extern const char *empty_barcode_received_event_msg;

extern const char *invalid_barcode_received_event_msg;
extern const char *decision_timeout_event_msg;

// The file must be open
/*@ requires \valid(the_file);
  @ requires File_Is_Open(the_file);
  @ ensures \result == true || \result == false;
*/
bool import_and_verify(log_file the_file);

/*@ requires Log_IO_Initialized;
  @ requires \valid(the_file);
  @ requires valid_read_string(the_name);
  @ requires \separated(the_file, the_name);
  @ assigns *the_file \from the_name, log_fs;
  @ ensures Log_IO_Initialized;
  @ ensures \result == true || \result == false;
*/
bool load_or_create(log_file the_file,
                    const log_name the_name,
                    const http_endpoint endpoint);

/*@ requires Log_IO_Initialized;
  @ requires valid_read_string(app_log_file_name);
  @ requires valid_read_string(system_log_file_name);
  @ assigns app_log_handle, system_log_handle \from log_fs;
  @ ensures Log_IO_Initialized;
  @ ensures \result == true || \result == false;
*/
bool load_or_create_logs(void);

/*@ requires Log_IO_Initialized;
  @ requires 0 < the_length && the_length <= LOG_ENTRY_LENGTH;
  @ requires \valid_read(the_message + (0 .. the_length - 1));
  @ requires \separated(&system_log_handle, the_message);
  @ assigns log_fs \from log_fs, the_message, system_log_handle;
  @ ensures Log_IO_Initialized;
  @ ensures \result == true || \result == false;
*/
bool log_system_message(const char *the_message, int the_length);

// @design abakst What information do we want to log here? The barcode?
typedef enum { APP_EVENT_BALLOT_USER_CAST=0,
               APP_EVENT_BALLOT_USER_SPOIL,
               APP_EVENT_NUM_EVENTS } app_event;

/*@ requires Log_IO_Initialized;
  @ requires 0 <= event && event < APP_EVENT_NUM_EVENTS;
  @ requires \valid_read(barcode + (0 .. barcode_length - 1));
  @ requires 0 < barcode_length && barcode_length <= BARCODE_MAX_LENGTH;
  @ assigns log_fs;
  @ ensures Log_IO_Initialized;
  @ ensures \result == true || \result == false;
*/
bool log_app_event(app_event event,
                   barcode_t barcode,
                   barcode_length_t barcode_length);

/*@ requires Log_IO_Initialized;
  // requires valid_read_string(the_message);
  @ requires \valid_read(the_message + (0 .. message_length - 1));
  @ requires 0 < message_length && message_length <= LOG_ENTRY_LENGTH;
  @ requires \separated(&system_log_handle, the_message);
  @ requires \valid(&the_state->L);
  @
  @ assigns the_state->L;
  @ assigns log_fs \from log_fs, the_message, system_log_handle;
  @
  @ ensures Log_IO_Initialized;
  @ ensures the_state->L != ABORT ==> the_state->L == \old(the_state->L);
*/
void log_or_abort(SBB_state *the_state, const char *the_message, int message_length);

/*@ requires \valid_read(barcode + (0 .. length-1));
  @ assigns \nothing;
  @ ensures \result == true || \result == false;
 */
bool barcode_cast_or_spoiled(barcode_t barcode, barcode_length_t length);

#define CHANGE_STATE(_state, _field, _new_state)                        \
    do { _state._field = _new_state;                                    \
        const char state_change_message[] = "State change: " #_field " := " #_new_state; \
        log_or_abort(&(_state), state_change_message, strlen(state_change_message));        \
    } while (0)
#endif
