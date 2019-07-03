#include "log.h"
#include "secure_log.h"
#include <stdio.h>
#include <stdlib.h>
void test_secure_log_security(const char *test_file_name)
{
    Log_Handle r_log;
    size_t N;

    Log_IO_Open(&r_log, test_file_name);

    N = Log_IO_Num_Base64_Entries(&r_log);

    printf("Number of entries=%zu\n", N);

    if (N >= 1)
    {
        if (verify_secure_log_security(&r_log))
        {
            printf("Log file security OK\n");
        }
        else
        {
            printf("Log file security FAILED\n");
        }
    }
}

int main(int argc, char *argv[])
{
    if (argc == 2)
    {
        if (Log_IO_File_Exists(argv[1]))
        {
            test_secure_log_security(argv[1]);
        }
        else
        {
            printf("file %s does not exist\n", argv[1]);
        }
    }
    else
    {
        printf("usage: test10 filename\n");
    }
    return 0;
}
