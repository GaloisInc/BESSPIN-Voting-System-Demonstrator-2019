#include "log.h"
#include <stdio.h>
// Non-empty log smoketest.
//Create a new, empty log, fill it with some log entries, validate it, and
//export it to a device.

int main(void)
{
  Log_Handle test_log;
  const log_entry test01_entry = "hello test01xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0
  const log_entry test02_entry = "hello test02xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

  
  //Log_IO_Initialize(); is not included in ASM

  // event - Create log.
  // Create a new, empty log,
  create_log (&test_log, "non_empty_log.txt");

  // event - Write log entry.
  write_entry (&test_log, test01_entry);
  
  // event - Write log entry.
  write_entry (&test_log, test02_entry);
  
  // event - Validate log.
  // Check whether or not log L is well-formed.
  validate_log(&test_log);

  // event - Export log.
  //Export log L to device D.  
  export_log(&test_log, /*a_target - needs to be defined in the second pass through this scenario*/);

 
  Log_IO_Close (&test_log);
}