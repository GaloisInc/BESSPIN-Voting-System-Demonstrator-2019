#include "base64.h"
#include <stdio.h>
#include <stdlib.h>

int main()
{
    char src_string[]="Dragan";
    char dst_string[1000];
    char decoded_string[1000];
    size_t len;
    
    len = *obtain_encode_buffer_size(src_string);
    encode(src_string,dst_string,len);
    printf("encoded=%s\n", dst_string);
   
    len = *obtain_decode_buffer_size(dst_string);

    decode(dst_string,decoded_string);
    printf("%s\n", decoded_string);
    /* code */
    return 0;
}