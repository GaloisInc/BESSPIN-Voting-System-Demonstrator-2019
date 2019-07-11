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
static const uint16_t PORT_NUMBER = 8066;

// We assume that a log entry data block can't be more than 9_999_999 bytes long, so
// we allocate up to 7 characters for this to be printed in decimal in the HTTP header.
static const size_t worst_case_data_length = 7;

#ifdef TARGET_OS_FreeRTOS

/////////////////////////////
// FreeRTOS implementation //
/////////////////////////////

/* FreeRTOS and IP stack includes. */
#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "list.h"

// Network configuration and addresses that are the same for all SBBs
static const uint8_t SBB_NetMask[4] = {255, 255, 255, 0};
static const uint8_t SBB_GatewayAddress[4] = {10, 10, 10, 1};
static const uint8_t SBB_DNSServerAddress[4] = {4, 2, 2, 2};
static const uint8_t Reporting_Server_IP_Address[4] = {10, 6, 6, 253};

// Network configuration and addresses that will be different for each SBB

// RCC made this up - to be confirmed
// Should be different for each SBB
static uint8_t This_SBB_IP_Address[4] = {10, 6, 6, 1};

// RCC No idea where these numbers came from - to be confirmed
// Should be different for each SBB
static uint8_t This_SBB_MAC_Address[6] = {0x00, 0x12, 0x13, 0x10, 0x15, 0x11};

void Log_Net_Initialize()
{
    debug_printf("FreeRTOS_IPInit\r\n");
    FreeRTOS_IPInit(This_SBB_IP_Address, SBB_NetMask, SBB_GatewayAddress,
                    SBB_DNSServerAddress, This_SBB_MAC_Address);
}

void Log_Net_Send(base64_secure_log_entry the_secure_log_entry,
                  http_endpoint endpoint, const char *remote_file_name)
{
    Socket_t xSocket;
    struct freertos_sockaddr xRemoteAddress;
    BaseType_t xBytesSent = 0;

    size_t xLenToSend;
    size_t xTotalLengthToSend;

    // request line and header
    const size_t FIXED_MESSAGE_SIZE =
        strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
        strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
        strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    const size_t MESSAGE_SIZE = FIXED_MESSAGE_SIZE + worst_case_data_length +
                                strlen(remote_file_name) + data_block_length;

    char pcBufferToTransmit[MESSAGE_SIZE];
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
        pcBufferToTransmit[i] = 0x00;
    }

    snprintf(pcBufferToTransmit, MESSAGE_SIZE, "%s%s%s%s%s%s%s%s%zu%s",
             REQUEST_LINE_1, remote_file_name, REQUEST_LINE_3, HEADER_1,
             HEADER_2, HEADER_3, HEADER_4, HEADER_5_1, data_block_length,
             DOUBLE_CRLF);

    // After the header has been written, we have N bytes of header,
    // occupying bytes 0 .. (N-1) of pcBufferToTransmit. So.. the first byte of the
    // data block will be at index N. We can use strlen to compute
    // this since pcBufferToTransmit was previously populated with all 0x00 bytes.
    size_t first_byte_of_data_index = strlen(pcBufferToTransmit);
    debug_printf("Length of header block is %zu\n", first_byte_of_data_index);

    // add base64_secure_log_entry to the pcBufferToTransmit
    memcpy(&pcBufferToTransmit[first_byte_of_data_index],
           &the_secure_log_entry.the_entry[0], LOG_ENTRY_LENGTH);

    size_t space_index = first_byte_of_data_index + LOG_ENTRY_LENGTH;
    debug_printf("space index is %zu\n", space_index);
    pcBufferToTransmit[space_index] = space;

    size_t hash_index = space_index + 1;
    debug_printf("hash index is %zu\n", hash_index);
    memcpy(&pcBufferToTransmit[hash_index], &the_secure_log_entry.the_digest[0],
           SHA256_BASE_64_DIGEST_LENGTH_BYTES);

    size_t new_line_index = hash_index + SHA256_BASE_64_DIGEST_LENGTH_BYTES;
    debug_printf("new line index is %zu\n", new_line_index);
    pcBufferToTransmit[new_line_index] = new_line;
    // If the final byte is at offset N in pcBufferToTransmit, then the xTotalLengthToSend number
    // of bytes to send is N + 1
    xTotalLengthToSend = new_line_index + 1;

    xRemoteAddress.sin_port = FreeRTOS_htons(PORT_NUMBER);
    // IP address needs to be modified for the test purpose
    // otherwise address can be taken from log_net.h uIPAddress
    // for now it is hardcoded before test.
    xRemoteAddress.sin_addr = FreeRTOS_inet_addr_quick(
        Reporting_Server_IP_Address[0], Reporting_Server_IP_Address[1],
        Reporting_Server_IP_Address[2], Reporting_Server_IP_Address[3]);

    // Create a socket.
    xSocket = FreeRTOS_socket(FREERTOS_AF_INET, FREERTOS_SOCK_STREAM,
                              FREERTOS_IPPROTO_TCP);
    configASSERT(xSocket != FREERTOS_INVALID_SOCKET);
    if (FreeRTOS_connect(xSocket, &xRemoteAddress, sizeof(xRemoteAddress)) == 0)
    {
        xLenToSend = 0;
        do
        {
            xBytesSent =
                FreeRTOS_send(/* The socket being sent to. */
                              xSocket,
                              /* The data being sent. */
                              pcBufferToTransmit + xLenToSend,
                              /* The remaining length of data to send. */
                              xTotalLengthToSend - xLenToSend,
                              /* ulFlags. */
                              0);
            if (xBytesSent < 0)
            {
                debug_printf("ERROR writing message to socket");
            }

            if (xBytesSent == 0)
            {
                break;
            }
            xLenToSend += xBytesSent;
        } while (xLenToSend < xTotalLengthToSend);
    }
    /* Initiate graceful shutdown. */
    FreeRTOS_shutdown(xSocket, FREERTOS_SHUT_RDWR);
    /* The socket has shut down and is safe to close. */
    FreeRTOS_closesocket(xSocket);
    return;
}

#else

//////////////////////////////////////////////
// POSIX implementation for MacOS and Linux //
//////////////////////////////////////////////

// @assume We have a POSIX I/O filesystem.
#include <netdb.h>      /* struct hostent, gethostbyname */
#include <netinet/in.h> /* struct sockaddr_in, struct sockaddr */
#include <stdio.h>      /* printf, sprintf */
#include <stdlib.h>     /* exit */
#include <string.h>     /* memcpy, memset */
#include <sys/socket.h> /* socket, connect */
#include <unistd.h>     /* read, write, close */

void Log_Net_Initialize() { return; }

void Log_Net_Send(base64_secure_log_entry the_secure_log_entry,
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
    memcpy(&message[first_byte_of_data_index],
           &the_secure_log_entry.the_entry[0], LOG_ENTRY_LENGTH);

    size_t space_index = first_byte_of_data_index + LOG_ENTRY_LENGTH;
    debug_printf("space index is %zu\n", space_index);
    message[space_index] = space;

    size_t hash_index = space_index + 1;
    debug_printf("hash index is %zu\n", hash_index);
    memcpy(&message[hash_index], &the_secure_log_entry.the_digest[0],
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
