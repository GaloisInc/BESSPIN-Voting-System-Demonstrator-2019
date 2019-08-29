#include "log.h"
#include <stdio.h>

int main(void)
{
    Log_Handle my_log;
    size_t num;

    Log_IO_Initialize();

    create_log(&my_log, "test1log.txt", HTTP_Endpoint_None);

    num = Log_IO_Num_Base64_Entries(&my_log);

    printf("Num entries in the files is %d\n", (int)num);

    Log_IO_Close(&my_log);
}
