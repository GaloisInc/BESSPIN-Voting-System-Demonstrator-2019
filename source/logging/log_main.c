/**
 * Smart Ballot Box Runtime Verification Test Harness
 * @refine logging/scenario.lando
 */

// General includes
#include <assert.h>
#include <stdio.h>

// Subsystem includes
#include "log_main.h"


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

uint8_t empty_log_entry[LOG_ENTRY_LENGTH];

static log_name generate_log_name(void) {
  return "smoketest.log";
}


static log_io_stream generate_log_io_stream(void) {
  log_name name = generate_log_name();
  Log_Handle *log;
  Log_IO_Create_New(log,name);
  #ifndef TARGET_OS_FreeRTOS
  log -> the_file = *stderr;
  #endif
  return log;
}

static log_entry *generate_log_entry(void) {
  return &empty_log_entry;
}

Log_FS_Result compare_logs_by_hash(log_name log_file, Log_Handle *second_log, log_io_stream stream)
{
  Log_Handle r_log;

  bool file_exists = Log_IO_File_Exists(log_file);
  
  // check that first log exists
  if (!file_exists) {
    #ifdef DEBUG
    #ifdef TARGET_OS_FreeRTOS
      FreeRTOS_debug_printf( ( "Failure - log file does not exists.\n" ) );
      f_printf(stream -> the_file, "Failure - log file does not exists.\n");
    #else
      fprintf(stream -> the_file, "Failure - log file does not exists");
    #endif
    #endif
    return LOG_FS_ERROR;
  }

  // open and read the log
  Log_IO_Open_Read(&r_log,log_file);
  
  secure_log_entry sle  = Log_IO_Read_Last_Entry(&r_log);

  // read compare hashes
  for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
  {

      if(sle.the_digest[i] != second_log->previous_hash[i]) 
      {
       #ifdef DEBUG
       #ifdef TARGET_OS_FreeRTOS
         FreeRTOS_debug_printf( ( "Failure - the hashes are not equal.\n" ) );
         f_printf(stream -> the_file, "Failure - the hashes are not equal.\n");

       #else
         fprintf(stream -> the_file, "Failure - the hashes are not equal.\n");
       #endif
       #endif       
       return LOG_FS_ERROR;
      }

  }
  return LOG_FS_OK;
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
  compare_logs_by_hash(the_log_name,my_second_log, a_target);
  Log_IO_Close (&my_first_log);
  return;
}

void Non_Empty_Log_Smoketest(const log_name the_log_name,
                             const log_io_stream a_target) {
  Log_Handle test_log;
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
  Log_IO_Initialize();
  create_log (&test_log, the_log_name);
  write_entry (&test_log, test01_entry);
  write_entry (&test_log, test02_entry);
  verify_log_well_formedness(&test_log);
  export_log(&test_log,a_target);
  log_file second_test_log = import_log(the_log_name);
  verify_log_well_formedness(second_test_log);
  compare_logs_by_hash(the_log_name,second_test_log, a_target);
  Log_IO_Close (&test_log);
  return;
}

int main(int argc, char* argv[]) {
  log_name smoketest_log = generate_log_name();
  
  // @todo kiniry The use of `stderr` and `printf` needs to be
  // refactored to use appropriate calls on FreeRTOS when building to
  // that target.
  log_io_stream stream = generate_log_io_stream();
  if (argc == 1)
    Empty_Log_Smoketest(smoketest_log, stream);
  else if (argc == 2 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(smoketest_log, stream);
  else if (argc == 3 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(argv[2], stream);
  else if (argc == 2 && strncmp("import_export_empty_log", argv[1], 23) == 0)
    Import_Export_Empty_Log(smoketest_log,stream);
  else if (argc == 2 && strncmp("non_empty_log_smoketest", argv[1], 23) == 0)
    Non_Empty_Log_Smoketest(smoketest_log, stream);
  else if (argc == 2 && strncmp("import_export_non_empty_log", argv[1], 27) == 0)
    Import_Export_Non_Empty_Log(smoketest_log, stream);
  else
    //printf("usage: log_main [smoketest [<log filename>]]\n");
    #ifdef DEBUG
    #ifdef TARGET_OS_FreeRTOS
    FreeRTOS_debug_printf( ( "usage: log_main [smoketest | import_export_empty_log | non_empty_log_smoketest | import_export_non_empty_log]\n" ) );
    #else
    fprintf(stderr, "usage: log_main [smoketest | import_export_empty_log | non_empty_log_smoketest | import_export_non_empty_log]\n");
    #endif
    #endif  
  return 0;
}
