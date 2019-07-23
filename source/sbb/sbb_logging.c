/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_t.h"
#include "sbb_logging.h"

const log_name system_log_file_name = "system_log.txt";
const log_name app_log_file_name    = "application_log.txt";

Log_Handle app_log_handle;
Log_Handle system_log_handle;

#ifndef FILESYSTEM_DUPLICATES
#define MAX_SCANNED_CODES 1000
uint8_t scanned_codes[MAX_SCANNED_CODES][BARCODE_MAX_LENGTH];
uint16_t num_scanned_codes = 0;
#endif // FILESYSTEM_DUPLICATES

// Each entry should be a 0-padded 256 uint8_t array according to the c specification.
const uint8_t app_event_entries[] = { 'C', 'S' };

bool import_and_verify(log_file the_file) {
    #ifdef SIMULATION
    (void) the_file;
    return false;
    #else
    bool b_success = false;

    if ( import_log(the_file) ) {
        b_success = verify_log_well_formedness(the_file);
    }

    return b_success;
    #endif
}

bool load_or_create(log_file the_file,
                    const log_name the_name,
                    const http_endpoint endpoint) {
    #ifdef SIMULATION
    (void) the_file;
    (void) the_name;
    (void) endpoint;
    return false;
    #else

    // @todo There is no API for opening a file for write, so we will overwrite for now
    bool b_success = true;

    if ( Log_IO_File_Exists(the_name) &&
         LOG_FS_OK == Log_IO_Open(the_file, the_name, endpoint) ) {
        b_success = import_and_verify(the_file);
    } else if ( LOG_FS_OK == create_log(the_file, the_name, endpoint) ) {
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

    if (load_or_create(&app_log_handle,
                       app_log_file_name,
                       HTTP_Endpoint_App_Log))
      {
        if (load_or_create(&system_log_handle,
                           system_log_file_name,
                           HTTP_Endpoint_Sys_Log))
          {
            b_success = true;
          }
      }

    return b_success;
    #endif
}

bool log_system_message(const char *new_entry, int length) {
    #ifdef SIMULATION
    (void) length;
    debug_printf("System LOG: %s\r\n", new_entry);
    return true;
    #else
    log_entry event_entry;
    memset(&event_entry[0], 0x20, sizeof(log_entry));
    memcpy(&event_entry[0], new_entry, length);
    Log_FS_Result res = write_entry(&system_log_handle, event_entry);
    return (res == LOG_FS_OK);
    #endif
}

void log_or_abort(SBB_state *the_local_state, const char *the_entry, int length) {
    debug_printf((char *)the_entry);
    #ifdef SIMULATION
    (void) the_local_state;
    (void) length;
    debug_printf("LOG: %s\r\n", the_entry);
    #else
    if (!log_system_message(the_entry, length)) {
        the_local_state->L = ABORT;
    }
    #endif
}

// @design abakst I think this is going to change as the logging implementation is fleshed out
// For example, we should be logging time stamps as well.

/*@ assigns scanned_codes[num_scanned_codes][0 .. BARCODE_MAX_LENGTH - 1];
  @ assigns num_scanned_codes;
*/
bool log_app_event(app_event event,
                   barcode_t barcode,
                   barcode_length_t barcode_length) {
    if ( num_scanned_codes >= MAX_SCANNED_CODES ) {
        return false;
    }

    if ( barcode_length + 2 < LOG_ENTRY_LENGTH ) {
        log_entry event_entry;
        memset(&event_entry[0], 0x20, sizeof(log_entry)); // pad with spaces
        event_entry[0] = app_event_entries[event];
        // we're guaranteed there are no spaces in the Base64 barcode, so it runs from [2] to
        // the next space in the entry
        memcpy(&event_entry[2], barcode, barcode_length);
#ifndef FILESYSTEM_DUPLICATES
        /*@ loop assigns i, scanned_codes[num_scanned_codes][0 .. BARCODE_MAX_LENGTH - 1];
          @ loop invariant 0 <= i && i <= barcode_length;
        */
        for (size_t i = 0; i < barcode_length; i++) {
            scanned_codes[num_scanned_codes][i] = (uint8_t)barcode[i];
        }
        /*@ loop assigns i, scanned_codes[num_scanned_codes][0 .. BARCODE_MAX_LENGTH - 1];
          @ loop invariant barcode_length <= i && i <= BARCODE_MAX_LENGTH;
        @*/
        for (size_t i = barcode_length; i < BARCODE_MAX_LENGTH; i++) {
            scanned_codes[num_scanned_codes][i] = 0x20;
        }
        num_scanned_codes++;
#endif
#ifdef SIMULATION
        debug_printf("LOG: %c %hhu", (char)app_event_entries[event], (uint8_t)barcode_length);
        for (size_t i = 0; i < barcode_length; i++) {
            debug_printf(" %hhx", (uint8_t)barcode[i]);
        }
        debug_printf("\r\n");
        return true;
#endif
        Log_FS_Result res = write_entry(&app_log_handle, event_entry);
        return (res == LOG_FS_OK);
    } else {
        return false;
    }
}

bool barcode_cast_or_spoiled(barcode_t barcode, barcode_length_t length) {
    bool b_found = false;
#ifdef FILESYSTEM_DUPLICATES
    size_t n_entries = Log_IO_Num_Base64_Entries(&app_log_handle);


    //@ assert b_found == true || b_found == false;
    if (length >= BARCODE_MAX_LENGTH) {
        debug_printf("barcode is too long, treated as duplicate");
        b_found = true; // treat too-long barcode as duplicate
    } else {
        debug_printf("scanning for duplicates, there are %d entries", n_entries);
        /** Scan the log backwards. The 0th entry is not a real entry to consider. */
        // note int32_t below because size_t is unsigned and subtraction 1 from it
        // yields a large positive number - hat tip to Haneef
        //@ assert b_found == true || b_found == false;
        /*@ loop assigns b_found;
          @ loop invariant b_found == true || b_found == false;
          @ loop invariant i_entry_no >= 1;
          @ loop invariant i_entry_no <= n_entries - 1;
        */
        for (int32_t i_entry_no = n_entries - 1; !b_found && (i_entry_no > 1); i_entry_no--) {
            debug_printf("scanning entry %d", i_entry_no);
            secure_log_entry secure_entry = Log_IO_Read_Base64_Entry(&app_log_handle, i_entry_no);
            b_found = true;
            // compare the barcodes up to the new barcode's length
            /*@ loop assigns i_barcode_idx, b_found;
              @ loop invariant i_barcode_idx <= length;
              @ loop invariant i_barcode_idx <= BARCODE_MAX_LENGTH;
              @ loop invariant i_barcode_idx >= 0;
            */
            for (size_t i_barcode_idx = 0;
                 b_found && (i_barcode_idx < length) && (i_barcode_idx < BARCODE_MAX_LENGTH);
                 i_barcode_idx++) {
                b_found = b_found && (secure_entry.the_entry[2 + i_barcode_idx] == barcode[i_barcode_idx]);
            }
            // ensure that the next character, if any, in the previously recorded barcode
            // is a space
            if (length + 1 < BARCODE_MAX_LENGTH) { // we haven't already checked the full width
                b_found = b_found && (secure_entry.the_entry[2 + length] == 0x20);
            }
        }
    }
#else // FILESYSTEM_DUPLICATES
    if (length >= BARCODE_MAX_LENGTH) {
        debug_printf("barcode is too long, treated as duplicate");
        b_found = true; // treat too-long barcode as duplicate
    } else if (num_scanned_codes >= MAX_SCANNED_CODES) {
        debug_printf("somehow scanned too many barcodes, treated as duplicate");
        b_found = true;
    } else {
        debug_printf("scanning for duplicates, there are %d entries", num_scanned_codes);
        /*@ loop assigns b_found;
          @ loop assigns i_entry_no;
          @ loop invariant b_found == true || b_found == false;
          @ loop invariant i_entry_no >= 0;
          @ loop invariant i_entry_no <= num_scanned_codes;
          @*/
        for (uint16_t i_entry_no = 0; !b_found && (i_entry_no < num_scanned_codes); i_entry_no++) {
            debug_printf("scanning entry %d", i_entry_no);
            b_found = true;
            /*@ loop assigns b_found;
              @ loop assigns i_barcode_idx;
              @ loop invariant b_found == true || b_found == false;
              @ loop invariant i_barcode_idx >= 0;
              @ loop invariant i_barcode_idx <= length;
              @*/
            for (size_t i_barcode_idx = 0; b_found && (i_barcode_idx < length); i_barcode_idx++) {
                b_found = b_found && (scanned_codes[i_entry_no][i_barcode_idx] == barcode[i_barcode_idx]);
            }
            // ensure that the next character, if any, in the previously recorded barcode
            // is a space
            if (length + 1 < BARCODE_MAX_LENGTH) { // we haven't already checked the full width
                b_found = b_found && (scanned_codes[i_entry_no][length] == 0x20);
            }
        }
        debug_printf("barcode is a duplicate: %d", b_found);
    }
    return b_found;
#endif // FILESYSTEM_DUPLICATES
}
