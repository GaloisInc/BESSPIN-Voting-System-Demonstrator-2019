/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_logging.h"

const log_name system_log_file_name = "system_log.txt";
const log_name app_log_file_name    = "application_log.txt";

Log_Handle app_log_handle;
Log_Handle system_log_handle;

const log_entry app_event_entries[] = { "Ballot cast.",
                                        "Ballot spoiled by user.",
                                        "Ballot spoiled (invalid barcode).",
                                        "Ballot spoiled (decision timeout)." };

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
    } else {
        // @todo Can this fail?
        create_log(the_file, the_name);
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

void log_system_message(const log_entry new_entry) {
    write_entry(&system_log_handle, new_entry);
}

// @design abakst I think this is going to change as the logging implementation is fleshed out
void log_app_event(app_event event) {
    write_entry(&app_log_handle, app_event_entries[event]);
}
