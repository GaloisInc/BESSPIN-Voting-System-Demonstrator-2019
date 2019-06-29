#include "base64.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void compare(const char *s1, const char *s2){
    if (strcmp(s1, s2) == 0) {
        printf("%s\n","Success!\n");
    }else {
        printf("%s\n","Failure!\n");
    }
}

int main()
{
    char dst[1000];
    char decoded_string[1000];
    char encoded_string[1000];
    size_t len;

	// padding 1 lendth 20

    printf("%s\n", "padding 1 lendth 20:");
    char src_string_padding_1_20[]="any carnal pleasure.";
    printf("Test string: %s\n", src_string_padding_1_20);
    
    len = *obtain_encode_buffer_size(src_string_padding_1_20);
    encode(src_string_padding_1_20, encoded_string, len);
    printf("encoded=%s\n", encoded_string);
   
    len = *obtain_decode_buffer_size(encoded_string);

    decode(encoded_string, decoded_string);
    printf("decoded=%s\n", decoded_string);
    compare(src_string_padding_1_20, decoded_string);

    // padding 2 lendth 19

    printf("%s\n", "padding 2 lendth 19:");
    char src_string_padding_2_19[]="any carnal pleasure";
    printf("Test string: %s\n", src_string_padding_2_19);
    
    len = *obtain_encode_buffer_size(src_string_padding_2_19);
    encode(src_string_padding_2_19, encoded_string, len);
    printf("encoded=%s\n", encoded_string);
   
    len = *obtain_decode_buffer_size(encoded_string);

    decode(encoded_string, decoded_string);
    printf("decoded=%s\n", decoded_string);
    compare(src_string_padding_2_19, decoded_string);

    // padding 0 lendth 18

    printf("%s\n", "padding 0 lendth 18:");
    char src_string_padding_0_18[]="any carnal pleasur";
    printf("Test string: %s\n", src_string_padding_0_18);
    
    len = *obtain_encode_buffer_size(src_string_padding_0_18);
    encode(src_string_padding_0_18, encoded_string, len);
    printf("encoded=%s\n", encoded_string);
   
    len = *obtain_decode_buffer_size(encoded_string);

    decode(encoded_string, decoded_string);
    printf("decoded=%s\n", decoded_string);
    compare(src_string_padding_0_18, decoded_string);

     // padding 1 lendth 17

    printf("%s\n", "padding 1 lendth 17:");
    char src_string_padding_1_17[]="any carnal pleasu";
    printf("Test string: %s\n", src_string_padding_1_17);
    
    len = *obtain_encode_buffer_size(src_string_padding_1_17);
    encode(src_string_padding_1_17, encoded_string, len);
    printf("encoded=%s\n", encoded_string);
   
    len = *obtain_decode_buffer_size(encoded_string);

    decode(encoded_string, decoded_string);
    printf("decoded=%s\n", decoded_string);
    compare(src_string_padding_1_17, decoded_string);

      // padding 2 lendth 16

    printf("%s\n", "padding 2 lendth 16:");
    char src_string_padding_2_16[]="any carnal pleas";
    printf("Test string: %s\n", src_string_padding_2_16);
    
    len = *obtain_encode_buffer_size(src_string_padding_2_16);
    encode(src_string_padding_2_16, encoded_string, len);
    printf("encoded=%s\n", encoded_string);
   
    len = *obtain_decode_buffer_size(encoded_string);

    decode(encoded_string, decoded_string);
    printf("decoded=%s\n", decoded_string);
    compare(src_string_padding_2_16, decoded_string);
     
    printf("%s\n", "test log entry:");
    char src_entry[]="hello "
        "test01xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo";
    
    len = *obtain_encode_buffer_size(src_entry);
    encode(src_entry, encoded_string, len);
    printf("encoded=%s\n", encoded_string);
   
    len = *obtain_decode_buffer_size(encoded_string);

    decode(encoded_string, decoded_string);
    printf("decoded=%s\n", decoded_string);

    printf("%s\n", "Test invariant decode ( encode )");
    compare(src_entry, decoded_string);

    printf("%s\n", "Test invariant encode ( decode )");
    len = *obtain_encode_buffer_size(decoded_string);
    encode(decoded_string, dst, len);
    compare(encoded_string, dst);

    printf("%s\n", "Test that 32 bytes become 44 bytes when Base64 encoded");
    char src_string_32[]="dependingonwhethertheobjectpoint";
    printf("Test string=%s\n", src_string_32);
    len = *obtain_encode_buffer_size(src_string_32);
    encode(src_string_32, encoded_string, len);
    if ( len == 45) {
        printf("buffer size=%zu\n", len );
        printf("base64 encoded length=%lu\n", strlen( encoded_string));
    }else {
        printf("Wrong number of Base64 encoded buffer size.");
    }

    
    return 0;
}