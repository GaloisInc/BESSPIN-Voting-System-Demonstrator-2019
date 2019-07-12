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

    create_log(&my_log, "test5log.txt", HTTP_Endpoint_None);
    write_entry(&my_log, second_entry);
    Log_IO_Close(&my_log);

    Log_IO_Open(&r_log, "test5log.txt");

    secure_log_entry _secure_log_entry = Log_IO_Read_Base64_Entry(&r_log, 0);
    uint8_t index = 0;
    // check digest
    for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
        if (_secure_log_entry.the_digest[i] == i)
        {
            index++;
        }
    }
    if (index == SHA256_DIGEST_LENGTH_BYTES)
    {
        printf("%s\n", "the_digest check of the first entry passed "
                       "successfully!"); /* code */
    }

    index = 0;

    for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
        if (_secure_log_entry.the_entry[i] <= (uint8_t)127)
        {
            index++;
        }
    }
    if (index == SHA256_DIGEST_LENGTH_BYTES)
    {
        printf("%s\n", "the_entry check of the first entry passed "
                       "successfully!"); /* code */
    }

    index = 0;

    index = 0;
    secure_log_entry _secure_log_entry1 = Log_IO_Read_Base64_Entry(&r_log, 1);
    for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
        if (_secure_log_entry1.the_digest[i] == (uint8_t)(255 - i))
        {
            index++;
        }
    }
    if (index == SHA256_DIGEST_LENGTH_BYTES)
    {
        printf("%s\n", "the_digest check of the second entry passed "
                       "successfully!"); /* code */
    }
    index = 0;
    for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
    {
        if (_secure_log_entry1.the_entry[i] <= (uint8_t)127)
        {
            index++;
        }
    }
    if (index == SHA256_DIGEST_LENGTH_BYTES)
    {
        printf("%s\n", "the_entry check of the second entry passed "
                       "successfully!"); /* code */
    }

    Log_IO_Close(&r_log);
}
