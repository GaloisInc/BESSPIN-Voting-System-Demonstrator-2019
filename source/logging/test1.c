#include "log.h"

int main(void)
{
  Log_Handle my_log;
  
  Log_IO_Initialize();

  create_log (&my_log, "newlog.txt");
  
}


