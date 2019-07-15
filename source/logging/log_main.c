/**
 * Smart Ballot Box Runtime Verification Test Harness
 * @refine logging/scenario.lando
 */

// General includes
#include <assert.h>
#include <stdio.h>

// Subsystem includes
#include "log_main.h"
#include "debug_io.h"

// constants

static const log_entry test01_entry =
        "hello "
        "test01xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

static const log_entry test02_entry =
        "hello "
        "test02xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0


// Helper functions

//uint8_t empty_log_entry[LOG_ENTRY_LENGTH];
Log_Handle log_handle;

static log_name generate_log_name(void) {
  return "test.log";
}


static log_io_stream generate_log_io_stream(void) {
  log_name name = generate_log_name();
  Log_IO_Create_New(&log_handle,name, HTTP_Endpoint_None);
  return &log_handle;
}

// static log_entry *generate_log_entry(void) {
//   return &empty_log_entry;
// }

Log_FS_Result compare_logs_by_hash(log_name log_file, Log_Handle *second_log, log_io_stream stream)
{
  Log_Handle r_log;

  // check that first log exists
  if (!Log_IO_File_Exists(log_file)) {
    debug_printf("Failure - log file does not exist.");
    debug_log_printf(stream, "Failure - log file does not exist.");
    return LOG_FS_ERROR;
  }

  // open and read the log
  Log_IO_Open(&r_log,log_file, HTTP_Endpoint_None);

  secure_log_entry sle  = Log_IO_Read_Last_Base64_Entry(&r_log);

  // read compare hashes
  for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
  {

      if (sle.the_digest[i] != second_log->previous_hash[i])
      {
        debug_printf("Failure - the hashes are not equal.");
        debug_log_printf(stream, "Failure - the hashes are not equal.");
        return LOG_FS_ERROR;
      }

  }
  return LOG_FS_OK;
}

// Scenarios

void Empty_Log_Smoketest(const log_name the_log_name,
                         const log_io_stream a_target) {
  Log_Handle test_log;
  Log_IO_Initialize();
  create_log(&test_log, the_log_name, HTTP_Endpoint_None);
  export_log(&test_log, a_target);
  Log_IO_Close(&test_log);
  return;
}

void Import_Export_Empty_Log(const log_name the_log_name,
                             const log_io_stream a_target) {
  Log_Handle first_log;
  Log_IO_Initialize();
  create_log(&first_log, the_log_name, HTTP_Endpoint_None);
  verify_log_well_formedness(&first_log);

  // RCC this test will be completed with both import and export are implemented
  //
  // export_log(&first_log, a_target);
  // log_file second_log = import_log(the_log_name);
  // verify_log_well_formedness(second_log);
  // compare_logs_by_hash(the_log_name, second_log, a_target);

  Log_IO_Close (&first_log);
  return;
}

void Non_Empty_Log_Smoketest(const log_name the_log_name,
                             const log_io_stream a_target) {
  Log_Handle test_log;
  Log_IO_Initialize();
  create_log (&test_log, the_log_name, HTTP_Endpoint_None);
  write_entry (&test_log, test01_entry);
  write_entry (&test_log, test02_entry);
  verify_log_well_formedness(&test_log);
  export_log(&test_log,a_target);
  Log_IO_Close (&test_log);
  return;
}

void Import_Export_Non_Empty_Log(const log_name the_log_name,
                                 const log_io_stream a_target) {
  Log_Handle test_log;
  Log_IO_Initialize();
  create_log (&test_log, the_log_name, HTTP_Endpoint_None);
  write_entry (&test_log, test01_entry);
  write_entry (&test_log, test02_entry);
  verify_log_well_formedness(&test_log);
  export_log(&test_log,a_target);

  // RCC this test will be completed with both import and export are implemented
  //
  // log_file second_test_log = import_log(the_log_name);
  // verify_log_well_formedness(second_test_log);
  // compare_logs_by_hash(the_log_name, second_test_log, a_target);

  Log_IO_Close (&test_log);
  return;
}

int main(int argc, char* argv[]) {
  log_name generated_name = generate_log_name();

  // @todo kiniry The use of `stderr` and `printf` needs to be
  // refactored to use appropriate calls on FreeRTOS when building to
  // that target.
  log_io_stream stream = generate_log_io_stream();
  if (argc == 1)
    Empty_Log_Smoketest(generated_name, stream);
  else if (argc == 2 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(generated_name, stream);
  else if (argc == 3 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(argv[2], stream);
  else if (argc == 2 && strncmp("import_export_empty_log", argv[1], 23) == 0)
    Import_Export_Empty_Log(generated_name, stream);
  else if (argc == 3 && strncmp("import_export_empty_log", argv[1], 23) == 0)
    Import_Export_Empty_Log(argv[2],stream);
  else if (argc == 2 && strncmp("non_empty_log_smoketest", argv[1], 23) == 0)
    Non_Empty_Log_Smoketest(generated_name, stream);
  else if (argc == 3 && strncmp("non_empty_log_smoketest", argv[1], 23) == 0)
    Non_Empty_Log_Smoketest(argv[2], stream);
  else if (argc == 2 && strncmp("import_export_non_empty_log", argv[1], 27) == 0)
    Import_Export_Non_Empty_Log(generated_name, stream);
  else if (argc == 3 && strncmp("import_export_non_empty_log", argv[1], 27) == 0)
    Import_Export_Non_Empty_Log(argv[2], stream);
  else
  {
    //printf("usage: log_main [smoketest [<log filename>]]\n");
    debug_printf("usage: log_main [smoketest | import_export_empty_log | non_empty_log_smoketest | import_export_non_empty_log]");
    debug_log_printf(stream, "usage: log_main [smoketest | import_export_empty_log | non_empty_log_smoketest | import_export_non_empty_log]");
  }
  return 0;
}
