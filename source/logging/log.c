/**
 * Smart Ballot Box API
 * @refine log.lando
 */

// General includes
#include <string.h>

// Subsystem includes
#include "log.h"
#include "secure_log.h"

Log_FS_Result create_log(Log_Handle *new_log_file,
                         const log_name the_log_name,
                         const http_endpoint endpoint)
{
    // TBD - what value should be here for production? See
    // Issue # 66 in GitLab.
    const log_entry first_entry =
        "hello "
        "worldxxxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnoooooooooooooooo"; // 256 chars not including final \0

    const secure_log_security_policy first_policy = {
        hashchain_sha2_256, no_provenance,     no_confidentiality,
        aes_cbc,            no_access_control, no_non_repudiation};

    Log_FS_Result create_result =
      create_secure_log(new_log_file, the_log_name, first_entry, first_policy, endpoint);

    return create_result;
}

Log_FS_Result write_entry(const log_file the_log, const log_entry a_log_entry)
{

    Log_FS_Result write_result = write_entry_to_secure_log(the_log, a_log_entry);

    return write_result;
}

bool verify_log_entry_well_formedness(const log_entry a_log_entry)
{
    (void)a_log_entry;
    return false;
}

void export_log(const log_file the_log, log_io_stream a_target) { 
    (void)the_log;
    (void)a_target;
    return;
}


bool verify_log_well_formedness(log_file the_log)
{
    return verify_secure_log_security(the_log);
}


bool import_log(log_file the_log_file)
{
  // Just verify that the file is well-formed.
  // If this returns TRUE, then the file is left open
  // with the file pointer at the END for subsequent
  // appending of further log entries.
  return verify_log_well_formedness(the_log_file);
}
