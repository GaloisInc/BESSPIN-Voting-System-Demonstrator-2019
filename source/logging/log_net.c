#include "log_net.h"
#include "debug_io.h"

#include <stdio.h>

static const char space = ' ';
static const char new_line = '\n';

static const char *REQUEST_LINE_1 = "POST /";
static const char *REQUEST_LINE_3 = " HTTP/1.1\r\n";
static const char *HEADER_1 = "Host: 10.6.6.253\r\n";
static const char *HEADER_2 = "User-Agent: sbb/2019\r\n";
static const char *HEADER_3 = "Accept: */*\r\n";
static const char *HEADER_4 = "Content-Type: application/octet-stream\r\n";
static const char *HEADER_5_1 = "Content-Length: ";
static const char *DOUBLE_CRLF = "\r\n\r\n";

static const size_t data_block_length = BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;

// We assume that a log entry data block can't be more than 9_999_999 bytes long, so
// we allocate up to 7 characters for this to be printed in decimal in the HTTP header.
static const size_t worst_case_data_length = 7;

#ifdef TARGET_OS_FreeRTOS

void Log_Net_Initialize()
{
    debug_printf("FreeRTOS_IPInit\r\n");
    FreeRTOS_IPInit(uIPAddress, uNetMask, uGatewayAddress, uDNSServerAddress,
                    uMACAddress);
}

void Log_Net_Send(base64_secure_log_entry secure_log_entry,
                  http_endpoint endpoint, const char *remote_file_name)
{
    return;
}

#else

void Log_Net_Initialize() { return; }

void Log_Net_Send(base64_secure_log_entry secure_log_entry,
                  http_endpoint endpoint, const char *remote_file_name)
{
    const size_t FIXED_MESSAGE_SIZE =
        strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
        strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
        strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    const size_t MESSAGE_SIZE = FIXED_MESSAGE_SIZE + worst_case_data_length +
                                strlen(remote_file_name) + data_block_length;

    char message[MESSAGE_SIZE];

    int sockfd;
    int bytes, sent, total;
    char *host = "localhost";
    struct hostent *server;
    struct sockaddr_in serv_addr;
    int PORT_NUMBER = 8066;

    debug_printf("MESSAGE_SIZE is %zu\n", MESSAGE_SIZE);

    // If user or test case has requested no HTTP echo of this log file,
    // then do nothing
    if (endpoint == HTTP_Endpoint_None)
    {
        return;
    }

    // Initialize message to all 0x00 so we can dynamically calculate the
    // length of the header
    for (size_t i = 0; i < MESSAGE_SIZE; i++)
    {
        message[i] = 0x00;
    }

    snprintf(message, MESSAGE_SIZE, "%s%s%s%s%s%s%s%s%zu%s", REQUEST_LINE_1,
             remote_file_name, REQUEST_LINE_3, HEADER_1, HEADER_2, HEADER_3,
             HEADER_4, HEADER_5_1, data_block_length, DOUBLE_CRLF);

    // After the header has been written, we have N bytes of header,
    // occupying bytes 0 .. (N-1) of message. So.. the first byte of the
    // data block will be at index N. We can use strlen to compute
    // this since message was previously populated with all 0x00 bytes.
    size_t first_byte_of_data_index = strlen(message);
    debug_printf("Length of header block is %zu\n", first_byte_of_data_index);

    // add base64_secure_log_entry to the message
    memcpy(&message[first_byte_of_data_index], &secure_log_entry.the_entry[0],
           LOG_ENTRY_LENGTH);

    size_t space_index = first_byte_of_data_index + LOG_ENTRY_LENGTH;
    debug_printf("space index is %zu\n", space_index);
    message[space_index] = space;

    size_t hash_index = space_index + 1;
    debug_printf("hash index is %zu\n", hash_index);
    memcpy(&message[hash_index], &secure_log_entry.the_digest[0],
           SHA256_BASE_64_DIGEST_LENGTH_BYTES);

    size_t new_line_index = hash_index + SHA256_BASE_64_DIGEST_LENGTH_BYTES;
    debug_printf("new line index is %zu\n", new_line_index);
    message[new_line_index] = new_line;

    // If the final byte is at offset N in message, then the total number
    // of bytes to send is N + 1
    total = new_line_index + 1;

    // create socket
    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0)
    {
        debug_printf("ERROR opening socket");
    }
    // lookup the ip address
    // notice this is localhost at the moment
    server = gethostbyname(host);
    if (server == NULL)
    {
        debug_printf("ERROR, no such host");
    }
    memset(&serv_addr, 0, sizeof(serv_addr));
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(PORT_NUMBER);
    memcpy(&serv_addr.sin_addr.s_addr, server->h_addr, server->h_length);

    // connect the socket
    if (connect(sockfd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0)
    {
        debug_printf("ERROR connecting the socket");
    }

    sent = 0;
    do
    {
        bytes = write(sockfd, message + sent, total - sent);
        if (bytes < 0)
        {
            debug_printf("ERROR writing message to socket");
        }
        if (bytes == 0)
        {
            break;
        }
        sent += bytes;
    } while (sent < total);

    close(sockfd);
    return;
}

#endif
