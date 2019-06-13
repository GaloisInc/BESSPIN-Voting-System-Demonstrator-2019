#include "log.h"

int main(void)
{
  Log_Handle my_log;

  const log_entry second_entry = "hello draganxxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

  
  Log_IO_Initialize();

  create_log (&my_log, "test2log.txt");

  write_entry (&my_log, second_entry);
	       
  Log_IO_Close (&my_log);
}


