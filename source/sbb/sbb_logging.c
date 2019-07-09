/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_logging.h"

const log_name system_log_file_name = "system_log.txt";
const log_name app_log_file_name    = "application_log.txt";

Log_Handle app_log_handle;
Log_Handle system_log_handle;

// Each entry should be a 0-padded 256 uint8_t array according to the c specification.
const log_entry app_event_entries[] = { "Ballot cast.",
                                        "Ballot spoiled by user." };

bool import_and_verify(log_file the_file) {
    bool b_success = false;

    if ( import_log(the_file) ) {
        b_success = verify_log_well_formedness(the_file);
    }

    return b_success;
}

bool load_or_create(log_file the_file, const log_name the_name) {
    // @todo There is no API for opening a file for write, so we will overwrite for now
    bool b_success = true;

    if ( Log_IO_File_Exists(the_name) &&
         LOG_FS_OK == Log_IO_Open(the_file, the_name) ) {
        b_success = import_and_verify(the_file);
    } else if ( LOG_FS_OK == create_log(the_file, the_name) ) {
        b_success = true;
    } else {
        b_success = false;
    }

    return b_success;
}

bool load_or_create_logs(void) {
    bool b_success = false;

    if ( load_or_create(&app_log_handle, app_log_file_name) ) {
        if ( load_or_create(&system_log_handle, system_log_file_name) ) {
            b_success = true;
        }
    }

    return b_success;
}

bool log_system_message(const log_entry new_entry) {
   Log_FS_Result res = write_entry(&system_log_handle, new_entry);

   return (res == LOG_FS_OK);
}

// @design abakst I think this is going to change as the logging implementation is fleshed out
// For example, we should be logging time stamps as well.
bool log_app_event(app_event event) {
    Log_FS_Result res = write_entry(&app_log_handle, app_event_entries[event]);

    return (res == LOG_FS_OK);
}

void log_or_abort(SBB_state *the_state, const log_entry the_entry) {
    debug_printf((char *)the_entry);
    if (!log_system_message(the_entry)) {
        the_state->L = ABORT;
    }
}
