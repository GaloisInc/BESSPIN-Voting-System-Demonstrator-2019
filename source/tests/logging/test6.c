#include "log.h"
#include <stdio.h>
#include <stdlib.h>
int main(void)
{
    Log_Handle my_log_first;
    Log_Handle r_log_first;

    Log_Handle my_log_second;
    Log_Handle r_log_second;

    const log_entry first_entry =
        "hello "
        "test61xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    const log_entry second_entry =
        "hello "
        "test62xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    // initialize create log write entry
    Log_IO_Initialize();
    create_log(&my_log_first, "test61log.txt", HTTP_Endpoint_None);
    write_entry(&my_log_first, first_entry);

    // create log write entry
    create_log(&my_log_second, "test62log.txt", HTTP_Endpoint_None);
    write_entry(&my_log_second, second_entry);

    Log_IO_Close(&my_log_first);
    Log_IO_Close(&my_log_second);

    Log_IO_Open(&r_log_first, "test61log.txt", HTTP_Endpoint_None);

    if (Log_IO_Num_Base64_Entries(&r_log_first) == 2)
    {
        printf("number of entries=%d - test passed successfully!\n", 2);
    }
    else
    {
        printf("%s\n", "test61 failed.");
    }
    Log_IO_Close(&r_log_first);

    Log_IO_Open(&r_log_second, "test62log.txt", HTTP_Endpoint_None);

    if (Log_IO_Num_Base64_Entries(&r_log_second) == 2)
    {
        printf("number of entries=%d - test passed successfully!\n", 2);
    }
    else
    {
        printf("%s\n", "test62 failed.");
    }
    Log_IO_Close(&r_log_second);
}
