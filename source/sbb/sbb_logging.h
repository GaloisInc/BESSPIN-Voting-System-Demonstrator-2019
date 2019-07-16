/**
 * Smart Ballot Box Logging Definitions
 */
#ifndef __SBB_LOGGING_
#define __SBB_LOGGING_

#include "sbb_t.h"
#include "log.h"
#include "debug_io.h"

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
bool import_and_verify(log_file the_file);

//@ requires true;
bool load_or_create(log_file the_file,
                    const log_name the_name,
                    const http_endpoint endpoint);

// For now, overwite the existing log
// @todo check for errors once it is possible to do so
//@ requires true;
bool load_or_create_logs(void);

//@ requires true;
bool log_system_message(const char *the_message);

// @design abakst What information do we want to log here? The barcode?
typedef enum { APP_EVENT_BALLOT_USER_CAST=0,
               APP_EVENT_BALLOT_USER_SPOIL,
               APP_EVENT_NUM_EVENTS } app_event;
bool log_app_event(app_event event,
                   barcode_t barcode,
                   barcode_length_t barcode_length);

/*@ requires \valid(the_state);
  @ assigns the_state->L;
  @ behavior log_error:
  @   ensures the_state->L == ABORT;
  @ behavior log_ok:
  @   ensures the_state->L == \old(the_state)->L;
  @ complete behaviors log_error, log_ok;
*/
void log_or_abort(SBB_state *the_state, const char *the_message);

bool barcode_cast_or_spoiled(barcode_t barcode, barcode_length_t length);

#define CHANGE_STATE(_state, _field, _new_state)                        \
    do { _state._field = _new_state;                                    \
        const char *state_change_message = "State change: " #_field " := " #_new_state; \
        log_or_abort(&(_state), state_change_message);                    \
    } while (0)
#endif
