#include "log.h"
#include <stdio.h>
#include <stdlib.h>

void print_entry (const log_entry l)
{
  for (size_t i = 0; i < LOG_ENTRY_LENGTH; i++)
    {
      printf ("%c", l[i]);
    }
  printf ("\n");
}

Log_FS_Result Test_Log_IO_Read_Base64_Entry(const char * test_file_name) {
	Log_Handle r_log;
	size_t N;
	secure_log_entry current_entry;

	Log_IO_Open(&r_log, test_file_name, HTTP_Endpoint_None);

	N = Log_IO_Num_Base64_Entries(&r_log);

	printf("Number of entries=%zu\n", N);

	for (size_t i = 1; i <= N; i++)
	{
		current_entry = Log_IO_Read_Base64_Entry(&r_log, N -i);

		printf("The entry: ");
		print_entry(current_entry.the_entry);

		printf("Hash starts with: %2X %2X %2X %2X\n",
                       current_entry.the_digest[0],
		       current_entry.the_digest[1],
                       current_entry.the_digest[2],
		       current_entry.the_digest[3]);
	}
	return LOG_FS_OK;
}

Log_FS_Result Test_Log_IO_Read_Last_Base64_Entry(const char * test_file_name) {
	Log_Handle r_log;
	secure_log_entry current_entry;
	size_t N = 0;

	Log_IO_Open(&r_log, test_file_name, HTTP_Endpoint_None);

  	N = Log_IO_Num_Base64_Entries(&r_log);

        if (N == 0)
          {
            printf("Failure. Log file %s cannot be empty.\n", test_file_name);
            return LOG_FS_ERROR;
          }

	printf("Number of entries=%zu\n", N);
	current_entry = Log_IO_Read_Last_Base64_Entry(&r_log);

        printf("The last entry: ");
        print_entry(current_entry.the_entry);

        printf("Hash starts with: %2X %2X %2X %2X\n", current_entry.the_digest[0],
               current_entry.the_digest[1], current_entry.the_digest[2],
               current_entry.the_digest[3]);

        if ( N == 1)
          {
            return LOG_FS_OK;
          }

	for (size_t i = 1; i <=  N - 1  ; i++)
          {
            current_entry = Log_IO_Read_Base64_Entry(&r_log, N - 1 - i);

            printf("The entry: ");
            print_entry(current_entry.the_entry);

            printf("Hash starts with: %2X %2X %2X %2X\n", current_entry.the_digest[0],
                   current_entry.the_digest[1], current_entry.the_digest[2],
                   current_entry.the_digest[3]);
          }

	return LOG_FS_OK;
}

int main(int argc, char* argv[]) {
	if (argc == 1)
	{
          printf("%s\n", "Failure. Please enter the log file name.");
	}
	else if (argc == 2 )
	{
          Log_IO_Initialize();
          if (Log_IO_File_Exists(argv[1]))
            {
              Test_Log_IO_Read_Base64_Entry(argv[1]);
              Test_Log_IO_Read_Last_Base64_Entry(argv[1]);
            }
          else
            {
              printf("Failure - log file %s does not exist.\n", argv[1]);
              return LOG_FS_ERROR;
            }

	}
    return 0;
}
