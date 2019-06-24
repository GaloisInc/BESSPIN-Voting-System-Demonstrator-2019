#include "log.h"
#include <stdio.h>
#include <stdlib.h>

uint8_t compare_logs_by_bytes(Log_Handle* first_log, Log_Handle *second_log)
{
    size_t      lsize_first, lsize_second; // log sizes
    uint8_t      byte1, byte2;
    
    // get the file size of the first log
    fseek (&first_log -> the_file, 0 , SEEK_END);
    lsize_first = ftell (&first_log -> the_file);
    rewind (&first_log -> the_file);
    
    // get the file size of the second log
    fseek (&second_log -> the_file , 0 , SEEK_END);
    lsize_second = ftell (&second_log -> the_file);
    rewind (&second_log -> the_file);

    if (lsize_first != lsize_second) {
        printf("%s\n","Failure - sizes are not equal" );
        return -1;
    }

    for (size_t i=0; i < lsize_first; i++) {
        fread(&byte1, 1, 1, &first_log -> the_file);
        fread(&byte2, 1, 1, &second_log -> the_file);
        if (byte1 != byte2) {
            printf("%s\n","Failure - bytes are not equal" );
            return -1;
        }
    }
    printf("%s\n","both logs are equal!");
    return 0;
}

int main(void)
{
    Log_Handle my_log_first;
    Log_Handle r_log_first;

    Log_Handle my_log_second;
    Log_Handle r_log_second;

    const log_entry first_entry =
        "hello "
        "test81xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    const log_entry second_entry =
        "hello "
        "test82xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    // initialize create log write entry
    Log_IO_Initialize();
    
    // two logs the same content

    create_log(&my_log_first, "test811log.txt");
    write_entry(&my_log_first, first_entry);
    Log_IO_Close(&my_log_first);
    
    
    create_log(&my_log_second, "test812log.txt");
    write_entry(&my_log_second, first_entry);
    Log_IO_Close(&my_log_second);


    Log_IO_Open_Read(&r_log_first, "test811log.txt");
    Log_IO_Open_Read(&r_log_second, "test812log.txt");
    compare_logs_by_bytes(&r_log_first,&r_log_second);
    Log_IO_Close(&my_log_first);
    Log_IO_Close(&my_log_second);
    
    // two logs different size

    create_log(&my_log_first, "test813log.txt");
    write_entry(&my_log_first, first_entry);
    write_entry(&my_log_first, first_entry);
    write_entry(&my_log_first, first_entry);
    Log_IO_Close(&my_log_first);
    
    
    create_log(&my_log_second, "test814log.txt");
    write_entry(&my_log_second, first_entry);
    Log_IO_Close(&my_log_second);


    Log_IO_Open_Read(&r_log_first, "test813log.txt");
    Log_IO_Open_Read(&r_log_second, "test814log.txt");
    compare_logs_by_bytes(&r_log_first,&r_log_second);
    Log_IO_Close(&my_log_first);
    Log_IO_Close(&my_log_second);

    // two logs different content the same size

    create_log(&my_log_first, "test815log.txt");
    write_entry(&my_log_first, first_entry);
    Log_IO_Close(&my_log_first);
    
    
    create_log(&my_log_second, "test816log.txt");
    write_entry(&my_log_second, second_entry);
    Log_IO_Close(&my_log_second);


    Log_IO_Open_Read(&r_log_first, "test815log.txt");
    Log_IO_Open_Read(&r_log_second, "test816log.txt");
    compare_logs_by_bytes(&r_log_first,&r_log_second);
    Log_IO_Close(&my_log_first);
    Log_IO_Close(&my_log_second);
}