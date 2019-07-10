#include "log.h"
#include <stdio.h>
#include <stdlib.h>
#include "log_net.h"
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
Log_FS_Result Test_Log_IO_Read_Base64_Entry_Send_Remotely(const char * test_file_name, char * remote_file_name) {
	Log_Handle r_log;
	size_t N;
	secure_log_entry current_entry;
	size_t olen;
    int r;
    
    log_name file_name = remote_file_name;

	Log_IO_Open(&r_log, test_file_name);
	if (!Log_IO_File_Exists(test_file_name)) {
    	printf("Failure - log file %s does not exist.\n", test_file_name);
    	 return LOG_FS_ERROR;
  	}
  	write_entry(&r_log, first_entry);
  	write_entry(&r_log, second_entry);

	N = Log_IO_Num_Base64_Entries(&r_log);

	printf("Number of entries=%zu\n", N);

    Log_NET_Initialize();
	for (size_t i = 1; i <= N; i++)
	{
		current_entry = Log_IO_Read_Base64_Entry(&r_log, N -i);
		
    	base64_secure_log_entry base_64_current_entry;

    	r = mbedtls_base64_encode(&base_64_current_entry.the_digest[0],
                              	SHA256_BASE_64_DIGEST_LENGTH_BYTES + 2, &olen,
                              	&current_entry.the_digest[0],
                              	SHA256_DIGEST_LENGTH_BYTES);
    	(void)r;

    	memcpy(&base_64_current_entry.the_entry[0], &current_entry.the_entry[0],
           	LOG_ENTRY_LENGTH);

		Log_NET_Send(base_64_current_entry, file_name);
		
	}
	return LOG_FS_OK;
}
int main(int argc, char* argv[]) {
	if (argc <= 2)
	{
          printf("%s\n", "Failure.Please enter the log file name and remote log file name.");
	}
	
	else if (argc == 3)
	{
          Log_IO_Initialize();
          Test_Log_IO_Read_Base64_Entry_Send_Remotely(argv[1], argv[2]);
	}
    return 0;
}