#include "log.h"
#include <stdio.h>
#include <stdlib.h>
void Test_Log_IO_Read_Last_Base64_Entry(const char * test_file_name) {
	Log_Handle r_log;
	size_t N;
	secure_log_entry current_entry;

	Log_IO_Open_Read(&r_log, test_file_name);
	
	N=Log_IO_Num_Base64_Entries(&r_log);

	printf("Number of entries=%zu\n", N);
	
	for (size_t i = 1; i <= N; i++)
	{
		current_entry = Log_IO_Read_Base64_Entry(&r_log, N -i);
		printf("the_entry:%s\n", current_entry.the_entry );
		printf("the_digest:%s\n", current_entry.the_digest );
	}

}

int main(int argc, char* argv[]) {
	if (argc == 1){
		Test_Log_IO_Read_Last_Base64_Entry("./test_data/good1.txt");
	}else if (argc == 2 && strncmp("good1", argv[1], 5) == 0){
		Test_Log_IO_Read_Last_Base64_Entry("./test_data/good1.txt");
	}else if (argc == 2 && strncmp("good2", argv[1], 5) == 0){
		Test_Log_IO_Read_Last_Base64_Entry("./test_data/good2.txt");
	}else if (argc == 2 && strncmp("good3", argv[1], 5) == 0){
		Test_Log_IO_Read_Last_Base64_Entry("./test_data/good3.txt");
	}else if (argc == 2 && strncmp("goodmany", argv[1], 8) == 0){
		Test_Log_IO_Read_Last_Base64_Entry("./test_data/goodmany.txt");
	}else
  {
    printf("usage: test9 [good1 | good2 | good3 | goodmany]"); 
  }
  return 0;
}