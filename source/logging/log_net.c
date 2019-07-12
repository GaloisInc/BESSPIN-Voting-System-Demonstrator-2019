///////////////////////////////////////////////////////
// Common include files needed by all implemenations //
///////////////////////////////////////////////////////

#include "log_net.h"
#include "../crypto/crypto.h"
#include "debug_io.h"

#include <stdio.h>

///////////////////////////////////////////////////
// Common constants needed by all implemenations //
///////////////////////////////////////////////////

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

//static const size_t data_block_length = BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;
static const uint16_t PORT_NUMBER = 8066;

// We assume that a log entry data block can't be more than 9_999_999 bytes long, so
// we allocate up to 7 characters for this to be printed in decimal in the HTTP header.
static const size_t worst_case_data_length = 7;

#ifdef TARGET_OS_FreeRTOS

//////////////////////////////////////////////
// FreeRTOS-specific includes and constants //
//////////////////////////////////////////////

/* FreeRTOS and IP stack includes. */
#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "list.h"

#define portable_assert(x) configASSERT(x)

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

#else

///////////////////////////////////////////
// POSIX-specific includes and constants //
///////////////////////////////////////////

#include <assert.h>
#include <netdb.h>      /* struct hostent, gethostbyname */
#include <netinet/in.h> /* struct sockaddr_in, struct sockaddr */
#include <stdio.h>      /* printf, sprintf */
#include <stdlib.h>     /* exit */
#include <string.h>     /* memcpy, memset */
#include <sys/socket.h> /* socket, connect */
#include <unistd.h>     /* read, write, close */

#define portable_assert(x) assert(x)

#endif


//////////////////////////////
// Exported function bodies //
//////////////////////////////

void Log_Net_Initialize()
{
#ifdef TARGET_OS_FreeRTOS
    debug_printf("FreeRTOS_IPInit");
    FreeRTOS_IPInit(This_SBB_IP_Address, SBB_NetMask, SBB_GatewayAddress,
                    SBB_DNSServerAddress, This_SBB_MAC_Address);
#endif
    // On POSIX, implementation is null
    return;
}


void Log_Net_Send(base64_secure_log_entry the_secure_log_entry,
                  const size_t padded_log_entry_length,
                  const size_t bytes_of_padding_required,
                  const http_endpoint endpoint, const char *remote_file_name)
{
    size_t total, current;

    // Calculate the length of the fixed parts of the HTTP POST Header
    const size_t FIXED_MESSAGE_SIZE =
        strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
        strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
        strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    const size_t content_length =
        padded_log_entry_length + BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH;

    const size_t MESSAGE_SIZE = FIXED_MESSAGE_SIZE + worst_case_data_length +
                                strlen(remote_file_name) + content_length;

    uint8_t Transmit_Buffer[MESSAGE_SIZE];

    // If user or test case has requested no HTTP echo of this log file,
    // then do nothing
    if (endpoint == HTTP_Endpoint_None)
    {
        return;
    }

    debug_printf("Transmit_Buffer is %zu", MESSAGE_SIZE);

    // Initialize Transmit_Buffer to all 0x00 so we can dynamically calculate the
    // length of the header
    for (size_t i = 0; i < MESSAGE_SIZE; i++)
    {
        Transmit_Buffer[i] = 0x00;
    }

    snprintf((char *)Transmit_Buffer, MESSAGE_SIZE, "%s%s%s%s%s%s%s%s%zu%s",
             REQUEST_LINE_1, remote_file_name, REQUEST_LINE_3, HEADER_1,
             HEADER_2, HEADER_3, HEADER_4, HEADER_5_1, content_length,
             DOUBLE_CRLF);

    // After the header has been written, we have N bytes of header,
    // occupying bytes 0 .. (N-1) of Transmit_Buffer. So.. the first byte of the
    // data block will be at index N. We can use strlen to compute
    // this since Transmit_Buffer was previously populated with all 0x00 bytes.
    size_t first_byte_of_data_index = strlen((char *)Transmit_Buffer);
    debug_printf("Length of header block is %zu", first_byte_of_data_index);

    // add the_secure_log_entry.the_entry to the Transmit_Buffer
    memcpy(&Transmit_Buffer[first_byte_of_data_index],
           &the_secure_log_entry.the_entry[0], LOG_ENTRY_LENGTH);

    // Add just the right number of spaces to make the data block,
    // spaces, hash and new_line an exact multiple of 16 bytes long.
    size_t space_index = first_byte_of_data_index + LOG_ENTRY_LENGTH;
    debug_printf("space index is %zu", space_index);
    for (size_t space_count = 0; space_count < bytes_of_padding_required;
         space_count++)
    {
        Transmit_Buffer[space_index] = space;
        space_index++;
    }

    // Add the Base64 encoded hash value from the_secure_log_entry.the_digest
    size_t hash_index = space_index;
    debug_printf("hash index is %zu", hash_index);
    memcpy(&Transmit_Buffer[hash_index], &the_secure_log_entry.the_digest[0],
           SHA256_BASE_64_DIGEST_LENGTH_BYTES);

    size_t new_line_index = hash_index + SHA256_BASE_64_DIGEST_LENGTH_BYTES;
    debug_printf("new line index is %zu", new_line_index);
    Transmit_Buffer[new_line_index] = new_line;

    // The total length of the data block, spaces, hash, new_line sequence
    // should be as expected and should be a multiple of AES_BLOCK_LENGTH_BYTES
    portable_assert((new_line_index - first_byte_of_data_index) + 1 ==
                    padded_log_entry_length);
    portable_assert(padded_log_entry_length % AES_BLOCK_LENGTH_BYTES == 0);

    // If the final byte is at offset N in Transmit_Buffer, then the current number
    // of bytes is N + 1
    current = new_line_index + 1;

    // Compute the AES_CBC_MAC of the whole block
    uint8_t binary_mac[AES_BLOCK_LENGTH_BYTES];
    aes_cbc_mac(&Transmit_Buffer[first_byte_of_data_index],
                padded_log_entry_length, &binary_mac[0]);

    // Turn that MAC into Base64 format
    uint8_t base64_mac[BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH];
    size_t olen;
    int r;
    r = mbedtls_base64_encode(&base64_mac[0],
                              BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH + 2, &olen,
                              &binary_mac[0], AES_BLOCK_LENGTH_BYTES);
    (void)r; // suppress warning on r unused.

    portable_assert(BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH == olen);

    total = current + BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH;

    // And append that MAC to the data to be sent
    memcpy(&Transmit_Buffer[current], &base64_mac[0],
           BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH);

    debug_printf("total bytes to send is %zu", total);


    // Socket creation, init and send

    {
#ifdef TARGET_OS_FreeRTOS
      // FreeRTOS-specific implementation of socket handling code
      Socket_t xSocket;
      struct freertos_sockaddr xRemoteAddress;
      BaseType_t xBytesSent = 0;
      size_t xLenToSend;

      xRemoteAddress.sin_port = FreeRTOS_htons(PORT_NUMBER);
      // IP address needs to be modified for the test purpose
      // otherwise address can be taken from log_net.h uIPAddress
      // for now it is hardcoded before test.
      xRemoteAddress.sin_addr = FreeRTOS_inet_addr_quick
        (Reporting_Server_IP_Address[0], Reporting_Server_IP_Address[1],
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
                              Transmit_Buffer + xLenToSend,
                              /* The remaining length of data to send. */
                              total - xLenToSend,
                              /* ulFlags. */
                              0);
              if (xBytesSent < 0)
                {
                  debug_printf("ERROR writing Transmit_Buffer to socket");
                }

              if (xBytesSent == 0)
                {
                  break;
                }
              xLenToSend += xBytesSent;
            } while (xLenToSend < total);
        }
      /* Initiate graceful shutdown. */
      FreeRTOS_shutdown(xSocket, FREERTOS_SHUT_RDWR);
      /* The socket has shut down and is safe to close. */
      FreeRTOS_closesocket(xSocket);

#else
      // POSIX-specific implementation of socket handling code
      int sockfd;
      int bytes, sent;
      char *host = "localhost";
      struct hostent *server;
      struct sockaddr_in serv_addr;

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
          bytes = write(sockfd, Transmit_Buffer + sent, total - sent);
          if (bytes < 0)
            {
              debug_printf("ERROR writing Transmit_Buffer to socket");
            }
          if (bytes == 0)
            {
              break;
            }
          sent += bytes;
        } while (sent < total);

      close(sockfd);

#endif // TARGET_OS_FreeRTOS

    }
    return;
}
