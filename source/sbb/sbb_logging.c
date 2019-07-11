/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_logging.h"

const log_name system_log_file_name = "system_log.txt";
const log_name app_log_file_name    = "application_log.txt";

Log_Handle app_log_handle;
Log_Handle system_log_handle;

// Each entry should be a 0-padded 256 uint8_t array according to the c specification.
const uint8_t app_event_entries[] = { 'C', 'S' };

bool import_and_verify(log_file the_file) {
    #ifdef SIMULATION
    return false;
    #else
    bool b_success = false;

    if ( import_log(the_file) ) {
        b_success = verify_log_well_formedness(the_file);
    }

    return b_success;
    #endif
}

bool load_or_create(log_file the_file, const log_name the_name) {
    #ifdef SIMULATION
    return false;
    #else
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
    #endif
}

bool load_or_create_logs(void) {
    #ifdef SIMULATION
    return true;
    #else
    bool b_success = false;

    if ( load_or_create(&app_log_handle, app_log_file_name) ) {
        if ( load_or_create(&system_log_handle, system_log_file_name) ) {
            b_success = true;
        }
    }

    return b_success;
    #endif
}

bool log_system_message(const log_entry new_entry) {
    #ifdef SIMULATION
    debug_printf("LOG: %s\r\n", new_entry);
    return true;
    #else
    Log_FS_Result res = write_entry(&system_log_handle, new_entry);
    return (res == LOG_FS_OK);
    #endif
}

void log_or_abort(SBB_state *the_state, const log_entry the_entry) {
    debug_printf((char *)the_entry);
    #ifdef SIMULATION
    debug_printf("LOG: %s\r\n", the_entry);
    #else
    if (!log_system_message(the_entry)) {
        the_state->L = ABORT;
    }
    #endif
}

// @design abakst I think this is going to change as the logging implementation is fleshed out
// For example, we should be logging time stamps as well.
bool log_app_event(app_event event,
                   barcode_t barcode,
                   barcode_length_t barcode_length) {
    if ( barcode_length + 2 < LOG_ENTRY_LENGTH ) {
        log_entry event_entry;
        event_entry[0] = app_event_entries[event];
        event_entry[1] = (uint8_t)barcode_length; // This is less than 256
        memcpy(&event_entry[2], barcode, barcode_length);
#ifdef SIMULATION
        debug_printf("LOG: %c %hhu", (char)app_event_entries[event], (uint8_t)barcode_length);
        for (size_t i = 0; i < barcode_length; ++i ) {
            debug_printf(" %hhx", (uint8_t)barcode[i]);
        }
        debug_printf("\r\n");
        return true;
#else
        Log_FS_Result res = write_entry(&app_log_handle, event_entry);
        return (res == LOG_FS_OK);
#endif
    } else {
        return false;
    }
}

bool barcode_cast_or_spoiled(barcode_t barcode, barcode_length_t length) {
    bool b_found = false;
    size_t n_entries = Log_IO_Num_Base64_Entries(&system_log_handle);

    /** Scan the log backwards. The 0th entry is not a real entry to consider. */
    for (size_t i_entry_no = n_entries - 1; !b_found && (i_entry_no > 1); --i_entry_no) {
        secure_log_entry secure_entry = Log_IO_Read_Base64_Entry(&system_log_handle, i_entry_no);

        if (secure_entry.the_entry[1] == (uint8_t)length) {
            b_found = true;
            for (size_t i_barcode_idx = 0; b_found && (i_barcode_idx < length); i_barcode_idx++) {
                b_found &= secure_entry.the_entry[2 + i_barcode_idx] == barcode[i_barcode_idx];
            }
        }
    }

    return b_found;
}
