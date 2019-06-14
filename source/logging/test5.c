 #include "log.h"
#include <stdio.h>
#include <stdlib.h>
int main(void)
{
 Log_Handle my_log;
 Log_Handle *r_log;

  //const log_entry second_entry = "hello draganxxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

  
  Log_IO_Initialize();

  create_log (&my_log, "test5log.txt");
  //write_entry (&my_log, second_entry);
  Log_IO_Close (&my_log);
  r_log = fopen("test5log.txt","r");   
  Log_IO_Read_Entry(r_log,1);
  Log_IO_Close (r_log);

}