#include "log.h"
#include <stdio.h>
// Empty log smoketest scenario.
// Create a new, empty log, validate it, and export it to a device.

int main(void)
{
  Log_Handle empty_log;
  
  //Log_IO_Initialize(); is not included in ASM

  // event - Create log.
  // Create a new, empty log,
  create_log (&empty_log, "empty_log.txt");
  
  // event - Validate log.
  // Check whether or not log is well-formed.
  validate_log(&empty_log);

  // event - Export log.
  //Export log L to device D.  
  export_log(&empty_log, /*a_target - needs to be defined in the second pass through this scenario*/);
  

  Log_IO_Close (&empty_log);
}
