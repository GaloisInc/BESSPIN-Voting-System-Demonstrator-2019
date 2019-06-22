#include "log.h"
#include <stdio.h>
// Import/export empty log scenario.
//Create a new, empty log, validate it, and export it to a device, import
//it from the device, validate it, and ensure that the two logs are equal.

int main(void)
{
  Log_Handle empty_log;
  
  //Log_IO_Initialize(); is not included in ASM

  // event - Create log.
  // Create a new, empty log,
  create_log (&empty_log, "empty_log.txt");
  
  // event - Validate log.
  // Check whether or not log L is well-formed.
  validate_log(&empty_log);

  // event - Export log.
  //Export log L to device D.  
  export_log(&empty_log, /*a_target this needs to be defined in the second pass through this scenario*/);

  // event - Import log.
  // Import log L from device D.

  // N.Y.I. 
  import_log(&empty_log);
  
  // event - Validate log.
  // Check whether or not log L is well-formed.
  validate_log(&empty_log);

  // ensure that the two logs are equal.
  // TBD

  Log_IO_Close (&empty_log);
}
