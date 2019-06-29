#include "base64.h"
#include <stdio.h>
#include <stdlib.h>

int main()
{
	char dst_string[1000];
    char decoded_string[1000];
    size_t len;

	// padding 1 lendth 20
	printf("%s\n", "padding 1 lendth 20:");
    char src_string_padding_1_20[]="any carnal pleasure.";
    
    len = *obtain_encode_buffer_size(src_string_padding_1_20);
    encode(src_string_padding_1_20,dst_string,len);
    printf("encoded=%s\n", dst_string);
   
    len = *obtain_decode_buffer_size(dst_string);

    decode(dst_string,decoded_string);
    printf("decoded=%s\n", decoded_string);


    // padding 2 lendth 19
    printf("%s\n", "padding 2 lendth 19:");
    char src_string_padding_2_19[]="any carnal pleasure";
    
    len = *obtain_encode_buffer_size(src_string_padding_2_19);
    encode(src_string_padding_2_19,dst_string,len);
    printf("encoded=%s\n", dst_string);
   
    len = *obtain_decode_buffer_size(dst_string);

    decode(dst_string,decoded_string);
    printf("decoded=%s\n", decoded_string);

    // padding 0 lendth 18

    printf("%s\n", "padding 0 lendth 18:");
    char src_string_padding_0_18[]="any carnal pleasur";
    
    len = *obtain_encode_buffer_size(src_string_padding_0_18);
    encode(src_string_padding_0_18,dst_string,len);
    printf("encoded=%s\n", dst_string);
   
    len = *obtain_decode_buffer_size(dst_string);

    decode(dst_string,decoded_string);
    printf("decoded=%s\n", decoded_string);


     // padding 1 lendth 17
    printf("%s\n", "padding 1 lendth 17:");
    char src_string_padding_1_17[]="any carnal pleasu";
    
    len = *obtain_encode_buffer_size(src_string_padding_1_17);
    encode(src_string_padding_1_17,dst_string,len);
    printf("encoded=%s\n", dst_string);
   
    len = *obtain_decode_buffer_size(dst_string);

    decode(dst_string,decoded_string);
    printf("decoded=%s\n", decoded_string);


      // padding 2 lendth 16
    printf("%s\n", "padding 2 lendth 16:");
    char src_string_padding_2_16[]="any carnal pleas";
    
    len = *obtain_encode_buffer_size(src_string_padding_2_16);
    encode(src_string_padding_2_16,dst_string,len);
    printf("encoded=%s\n", dst_string);
   
    len = *obtain_decode_buffer_size(dst_string);

    decode(dst_string,decoded_string);
    printf("decoded=%s\n", decoded_string);
    /* code */
     
    printf("%s\n", "test log entry:");
    char src_entry[]="hello "
        "test01xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo";
    
    len = *obtain_encode_buffer_size(src_entry);
    encode(src_entry,dst_string,len);
    printf("encoded=%s\n", dst_string);
   
    len = *obtain_decode_buffer_size(dst_string);

    decode(dst_string,decoded_string);
    printf("decoded=%s\n", decoded_string);



    return 0;
}