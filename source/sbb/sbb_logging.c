/**
 * Smart Ballot Box Logging Implementation
 */
#include "sbb_logging.h"

const log_name system_log_file_name = "system_log.txt";
const log_name app_log_file_name    = "application_log.txt";

Log_Handle app_log_handle;
Log_Handle system_log_handle;

void load_or_create(log_file the_file, const log_name the_name) {
    // @todo There is no API for opening a file for write, so we will overwrite for now
    if ( false && Log_IO_File_Exists(the_name) ) {
        // Import log is not implemented
        // *the_file = import_log(the_name);
        // Log_IO_Open_Read(the_file, the_name);
        // verify_log_well_formedness(*the_file);
        // @todo handle errors when this procedure is updated
    } else {
        create_log(the_file, the_name);
        // @todo handle errors when this procedure is updated
    }
}

void load_or_create_logs(void) {
    load_or_create(&app_log_handle, app_log_file_name);
    load_or_create(&system_log_handle, system_log_file_name);
}

void log_system_message(const log_entry new_entry) {
    write_entry(&system_log_handle, new_entry);
}
