#include "log.h"
#include <stdio.h>
#include <stdlib.h>
Log_FS_Result Test_Log_IO_Read_Base64_Entry(const char * test_file_name) {
	Log_Handle r_log;
	size_t N;
	secure_log_entry current_entry;

	Log_IO_Open_Read(&r_log, test_file_name);
	if (!Log_IO_File_Exists(test_file_name)) {
    	printf("Failure - log file %s does not exist.\n", test_file_name);
    	 return LOG_FS_ERROR;
  	}
	
	N=Log_IO_Num_Base64_Entries(&r_log);

	printf("Number of entries=%zu\n", N);
	
	for (size_t i = 1; i <= N; i++)
	{
		current_entry = Log_IO_Read_Base64_Entry(&r_log, N -i);
		printf("The entry:%s\n", current_entry.the_entry );
		printf("Hash starts with: %2X %2X %2X %2X\n", current_entry.the_digest[0], 
			  current_entry.the_digest[1], current_entry.the_digest[2], 
			  current_entry.the_digest[3]);
	}
	return LOG_FS_OK;
}

Log_FS_Result Test_Log_IO_Read_Last_Base64_Entry(const char * test_file_name) {
	Log_Handle r_log;
	secure_log_entry current_entry;

	Log_IO_Open_Read(&r_log, test_file_name);
	if (!Log_IO_File_Exists(test_file_name)) {
    	printf("Failure - log file %s does not exist.\n", test_file_name);
    	 return LOG_FS_ERROR;
  	}

	current_entry = Log_IO_Read_Last_Base64_Entry(&r_log);
	printf("The last entry:%s\n", current_entry.the_entry );
	printf("Hash starts with: %2X %2X %2X %2X\n", current_entry.the_digest[0], 
		  current_entry.the_digest[1], current_entry.the_digest[2], 
		  current_entry.the_digest[3]);

	return LOG_FS_OK;
}

int main(int argc, char* argv[]) {
	if (argc == 1){
		printf("%s\n", "Failure.Please enter the log file name.");
	}else if (argc == 2 ) {
		Test_Log_IO_Read_Base64_Entry(argv[1]);
		Test_Log_IO_Read_Last_Base64_Entry(argv[1]);
	}
  return 0;
}