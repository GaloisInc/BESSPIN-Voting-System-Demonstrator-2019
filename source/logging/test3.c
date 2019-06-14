#include "log.h"

int main(void)
{
  Log_Handle my_log;

  const log_entry second_entry = "hello rod   xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

  
  Log_IO_Initialize();

  create_log (&my_log, "test3log.txt");

  write_entry (&my_log, second_entry);
	       
  Log_IO_Close (&my_log);

  // It should be there so
  if (Log_IO_File_Exists ("test3log.txt"))
    printf ("test3log.txt exists - pass\n");
  else
    printf ("test3log.txt does not exist - fail\n");
  
  // Now test a file that should not be there
  if (Log_IO_File_Exists ("non_existant.txt"))
    printf ("non_existant.txt exists - fail\n");
  else
    printf ("non_existant.txt does not exist - pass\n");
	
	
}


