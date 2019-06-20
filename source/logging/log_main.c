/**
 * Smart Ballot Box Runtime Verification Test Harness
 * @refine logging/scenario.lando
 */

// General includes
#include <assert.h>
#include <stdio.h>

// Subsystem includes
#include "log_main.h"

void Empty_Log_Smoketest(const log_name the_log_name,
                         const log_io_stream a_target) {
  // @todo kiniry This will only work on FreeRTOS.
  Log_Handle my_log;
  Log_IO_Initialize();
  create_log(&my_log, the_log_name);
  export_log(&my_log, a_target);
  return;
}

void Import_Export_Empty_Log(const log_name the_log_name,
                             const log_io_stream a_target) {
  assert(false && "unimplemented");
  //@ assert false;
  return;
}

void Non_Empty_Log_Smoketest(const log_name the_log_name,
                             const log_io_stream a_target) {
  assert(false && "unimplemented");
  //@ assert false;
  return;
}

void Import_Export_Non_Empty_Log(const log_name the_log_name,
                                 const log_io_stream a_target) {
  assert(false && "unimplemented");
  //@ assert false;
  return;
}

int main(int argc, char* argv[]) {
  char* smoketest_log = "smoketest.log";
  
  // @todo kiniry The use of `stderr` and `printf` needs to be
  // refactored to use appropriate calls on FreeRTOS when building to
  // that target.
  if (argc == 1)
    Empty_Log_Smoketest(smoketest_log, stderr);
  else if (argc == 2 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(smoketest_log, stderr);
  else if (argc == 3 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(argv[2], stderr);
  else
    printf("usage: log_main [smoketest [<log filename>]]\n");
  return 0;
}
