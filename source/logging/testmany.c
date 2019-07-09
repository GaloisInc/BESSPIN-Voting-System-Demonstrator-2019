#include "log.h"
#include <stdio.h>

int main(void)
{
    Log_Handle my_log;
    size_t num;

    const log_entry second_entry =
        "hello "
        "draganxxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    log_entry next_entry =
        "hello rod   "
        "xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddee"
        "eeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiii"
        "iiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmm"
        "mmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    Log_IO_Initialize();

    create_log(&my_log, "testmanylog.txt");

    write_entry(&my_log, second_entry);
    write_entry(&my_log, next_entry);
    next_entry[9] = '2';
    write_entry(&my_log, next_entry);
    next_entry[9] = '3';
    write_entry(&my_log, next_entry);
    next_entry[9] = '4';
    write_entry(&my_log, next_entry);
    next_entry[9] = '5';
    write_entry(&my_log, next_entry);
    next_entry[9] = '6';
    write_entry(&my_log, next_entry);

    num = Log_IO_Num_Base64_Entries(&my_log);

    printf("Num entries in the files is %d\n", (int)num);

    Log_IO_Close(&my_log);

    // It should be there so
    if (Log_IO_File_Exists("test3log.txt"))
        printf("test3log.txt exists - pass\n");
    else
        printf("test3log.txt does not exist - fail\n");

    // Now test a file that should not be there
    if (Log_IO_File_Exists("non_existant.txt"))
        printf("non_existant.txt exists - fail\n");
    else
        printf("non_existant.txt does not exist - pass\n");
}
