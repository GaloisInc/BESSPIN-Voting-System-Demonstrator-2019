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
  assert(false && "unimplemented");
  //@ assert false;
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
  // @todo kiniry The use of STDERR and printf needs to be refactored
  // to an appropriate calls on FreeRTOS.
  if (argc == 1)
    Empty_Log_Smoketest("smoketest.log", stderr);
  else if (argc == 2 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest("smoketest.log", stderr);
  else if (argc == 3 && strncmp("smoketest", argv[1], 9) == 0)
    Empty_Log_Smoketest(argv[2], stderr);
  else
    printf("usage: log_main [smoketest [<log filename>]]\n");
  return 0;
}
