#include "log.h"
#include <stdio.h>
#include <stdlib.h>
int main(void)
{
    Log_Handle my_log;
    Log_Handle r_log;

    const log_entry second_entry =
        "hello "
        "draganxxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    Log_IO_Initialize();

    create_log(&my_log, "test4log.txt");
    write_entry(&my_log, second_entry);
    Log_IO_Close(&my_log);

    Log_IO_Open_Read(&r_log, "test4log.txt");

    if (Log_IO_Num_Base64_Entries(&r_log) == 2)
    {
        printf("number of entries=%d - test passed successfully!\n", 2);
    }
    else
    {
        printf("%s\n", "test4 failed.");
    }
    Log_IO_Close(&r_log);
}
