#include "log.h"
#include "secure_log.h"
#include <stdio.h>
#include <stdlib.h>

const log_entry second_entry =
  "Append Log 1"
  "xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddee"
  "eeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiii"
  "iiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmm"
  "mmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

const log_entry third_entry =
  "Append Log 2"
  "xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccddddddddddddddddee"
  "eeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhiiiiiiii"
  "iiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmmmmmmmm"
  "mmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0


void test_import(const char *test_file_name)
{
    Log_Handle r_log;

    Log_IO_Open(&r_log, test_file_name, HTTP_Endpoint_None);

    if (import_log (&r_log))
      {
        printf("File imported OK... trying to append\n");

        write_entry(&r_log, second_entry);
        write_entry(&r_log, third_entry);

      }
    else
      {
        printf("File import - verification failed\n");
      }

    Log_IO_Close (&r_log);
}

int main(int argc, char *argv[])
{
    if (argc == 2)
    {
        Log_IO_Initialize();
        if (Log_IO_File_Exists(argv[1]))
        {
            test_import(argv[1]);
        }
        else
        {
            printf("file %s does not exist\n", argv[1]);
        }
    }
    else
    {
        printf("usage: testimport filename\n");
    }
    return 0;
}
