/**
 * Smart Ballot Box Runtime Verification Test Harness
 * @refine logging/scenario.lando
 */

// General includes
#include <assert.h>
#include <stdio.h>

// Subsystem includes
#include "log_main.h"

// Helper functions

uint8_t empty_log_entry[LOG_ENTRY_LENGTH];

static log_name generate_log_name(void) {
  return "";
}

/*
static log_io_stream generate_log_io_stream(void) {
  return stderr;
}
*/

static log_entry *generate_log_entry(void) {
  return &empty_log_entry;
}

// Scenarios

void Empty_Log_Smoketest(const log_name the_log_name,
                         const log_io_stream a_target) {
  Log_Handle my_log;
  Log_IO_Initialize();
  create_log(&my_log, the_log_name);
  export_log(&my_log, a_target);
  return;
}

void Import_Export_Empty_Log(const log_name the_log_name,
                             const log_io_stream a_target) {
  Log_Handle my_first_log;
  Log_IO_Initialize();
  create_log(&my_first_log, the_log_name);
  verify_log_well_formedness(&my_first_log);
  export_log(&my_first_log, a_target);
  log_file my_second_log = import_log(the_log_name);
  verify_log_well_formedness(my_second_log);
  // @todo kiniry We have no means by which to compare the two logs.
  return;
}

void Non_Empty_Log_Smoketest(const log_name the_log_name,
                             const log_io_stream a_target) {
  Log_Handle test_log;
  
  const log_entry test01_entry =
        "hello "
        "test01xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

  const log_entry test02_entry =
        "hello "
        "test02xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

  Log_IO_Initialize();
  create_log (&test_log, the_log_name);
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
  
  const log_entry test01_entry =
        "hello "
        "test01xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0
  
  const log_entry test02_entry =
        "hello "
        "test02xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0
  
  Log_IO_Initialize();
  create_log (&test_log, the_log_name);
  write_entry (&test_log, test01_entry);
  write_entry (&test_log, test02_entry);
  verify_log_well_formedness(&test_log);
  export_log(&test_log,a_target);
  log_file second_test_log = import_log(the_log_name);
  verify_log_well_formedness(second_test_log);
  // @todo kiniry/dragan We have no means by which to compare the two logs.
  Log_IO_Close (&test_log);
  return;
}

int main(int argc, char* argv[]) {
  char* smoketest_log = "smoketest.log";
  
  // @todo kiniry The use of `stderr` and `printf` needs to be
  // refactored to use appropriate calls on FreeRTOS when building to
  // that target.
  /*
  if (argc == 1)
    Empty_Log_Smoketest(smoketest_log, stderr);
  else if (argc == 2 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(smoketest_log, stderr);
  else if (argc == 3 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(argv[2], stderr);
  else if (argc == 2 && strncmp("import_export_empty_log", argv[1], 23) == 0)
    Import_Export_Empty_Log(smoketest_log,stderr);
  else if (argc == 2 && strncmp("non_empty_log_smoketest", argv[1], 23) == 0)
    Non_Empty_Log_Smoketest(smoketest_log, stderr);
  else if (argc == 2 && strncmp("import_export_non_empty_log", argv[1], 27) == 0)
    Import_Export_Non_Empty_Log(smoketest_log, stderr);
  else
    //printf("usage: log_main [smoketest [<log filename>]]\n");
    printf("usage: software_main [smoketest | import_export_empty_log | non_empty_log_smoketest | import_export_non_empty_log]\n");
  */
  return 0;
}
