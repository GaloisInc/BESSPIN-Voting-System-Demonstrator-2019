#include "log.h"
#include <stdio.h>
// Import/export non-empty log.
// Create a new, empty log, fill it with some log entries, export it to a
// device, import it from the device, validate it, and ensure that the
// two logs are equal.

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

  // event - Import log.
  // Import log L from device D.

  // N.Y.I. 
  import_log(&test_log);

  // event - Validate log.
  // Check whether or not log L is well-formed.
  validate_log(&test_log);
  

  // ensure that the two logs are equal.
  // TBD


  Log_IO_Close (&test_log);
}