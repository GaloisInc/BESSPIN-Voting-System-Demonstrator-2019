#include "logging/log.h"
#include "logging/log_net.h"
#include <string.h>

///////////////////////////////////////////////////
// Common constants needed by all implemenations //
///////////////////////////////////////////////////

static const char *REQUEST_LINE_1 = "POST /";
static const char *REQUEST_LINE_3 = " HTTP/1.1\r\n";
static const char *HEADER_1 = "Host: 192.168.1.1\r\n";
static const char *HEADER_2 = "User-Agent: sbb/2019\r\n";
static const char *HEADER_3 = "Accept: */*\r\n";
static const char *HEADER_4 = "Content-Type: application/octet-stream\r\n";
static const char *HEADER_5_1 = "Content-Length: ";
static const char *DOUBLE_CRLF = "\r\n\r\n";

// We assume that data blocks can't be more than 9_999_999 bytes long, so
// we allocate up to 7 characters for this to be printed in decimal in the HTTP header.
static const size_t worst_case_data_length = 7;

/////////////////////////////
// Local ACSL declarations //
/////////////////////////////

/*@
    logic integer POST_Header_Fixed_Part_Length =
        strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
        strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
        strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    logic integer POST_Header_Min_Length = POST_Header_Fixed_Part_Length +
                                           worst_case_data_length +
                                           LOG_FILE_NAME_MIN_LENGTH;

    logic integer POST_Header_Max_Length = POST_Header_Fixed_Part_Length +
                                           worst_case_data_length +
                                           LOG_FILE_NAME_MAX_LENGTH;

*/


/////////////////////////////////
// Local function declarations //
/////////////////////////////////

/*@ requires \valid(Transmit_Buffer + (0 .. Transmit_Buffer_Length - 1));
  requires valid_log_file_name(log_file_name);
  requires valid_read_string(REQUEST_LINE_1);
  requires valid_read_string(REQUEST_LINE_3);
  requires valid_read_string(HEADER_1);
  requires valid_read_string(HEADER_2);
  requires valid_read_string(HEADER_3);
  requires valid_read_string(HEADER_4);
  requires valid_read_string(HEADER_5_1);
  requires valid_read_string(DOUBLE_CRLF);
  ensures valid_string((char *) Transmit_Buffer);
  ensures strlen((char *) Transmit_Buffer) >= POST_Header_Min_Length;
  ensures strlen((char *) Transmit_Buffer) <= POST_Header_Max_Length;
*/
void Initialize_POST_Header(const char *log_file_name,        // in
                            size_t data_length,
                            uint8_t *Transmit_Buffer,         // out by ref
                            size_t Transmit_Buffer_Length);   // in


void Initialize_POST_Header(const char *log_file_name,     // in
                            size_t data_length,
                            uint8_t *Transmit_Buffer,      // out by ref
                            size_t Transmit_Buffer_Length) // in
{
    // Initialize Transmit_Buffer to all 0x00 so we can dynamically calculate the
    // length of the header
    /*@
      loop invariant 0 <= i <= Transmit_Buffer_Length;
      loop invariant \valid(Transmit_Buffer + (0 .. Transmit_Buffer_Length - 1));
      loop assigns i, Transmit_Buffer[0 .. Transmit_Buffer_Length - 1];
      loop variant Transmit_Buffer_Length - i;
    */
    for (size_t i = 0; i < Transmit_Buffer_Length; i++) {
        Transmit_Buffer[i] = 0x00;
    }

    snprintf((char *)Transmit_Buffer, Transmit_Buffer_Length,
             "%s%s%s%s%s%s%s%s%zu%s",
             REQUEST_LINE_1, log_file_name,
             REQUEST_LINE_3, HEADER_1, HEADER_2, HEADER_3, HEADER_4, HEADER_5_1,
             data_length, DOUBLE_CRLF);
}

// Form a POST request to stream->filename containing Tx_Buffer
// requires buffer_size <= 9999999;
void Log_Net_Send(const char *remote_file_name, uint8_t *Transmit_Buffer, size_t buffer_size)
{
    const size_t HTTP_Header_Fixed_Part_Length =
        strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
        strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
        strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    const size_t Post_Buffer_Size =
        HTTP_Header_Fixed_Part_Length
        + worst_case_data_length
        + strlen(remote_file_name)
        + buffer_size;
    uint8_t Post_Buffer[Post_Buffer_Size];

    Initialize_POST_Header(remote_file_name, buffer_size, Post_Buffer, Post_Buffer_Size);

    size_t data_index = strlen((char *)Post_Buffer);
    memcpy(&Post_Buffer[data_index], Transmit_Buffer, buffer_size);

    osd_Log_Net_Send(Post_Buffer, Post_Buffer_Size);
}
