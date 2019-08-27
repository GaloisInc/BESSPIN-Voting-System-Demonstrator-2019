///////////////////////////////////////////////////////
// Common include files needed by all implemenations //
///////////////////////////////////////////////////////

#include "crypto/crypto.h"
#include "logging/log_net.h"
#include "logging/debug_io.h"
#include "logging/log_io.h"

#include <stdio.h>

///////////////////////////////////////////////////
// Common constants needed by all implemenations //
///////////////////////////////////////////////////
// Unused?
// static const char space = ' ';
// static const char new_line = '\n';

// static const char *REQUEST_LINE_1 = "POST /";
// static const char *REQUEST_LINE_3 = " HTTP/1.1\r\n";
// static const char *HEADER_1 = "Host: 10.5.5.1\r\n";
// static const char *HEADER_2 = "User-Agent: sbb/2019\r\n";
// static const char *HEADER_3 = "Accept: */*\r\n";
// static const char *HEADER_4 = "Content-Type: application/octet-stream\r\n";
// static const char *HEADER_5_1 = "Content-Length: ";
// static const char *DOUBLE_CRLF = "\r\n\r\n";

//static const size_t data_block_length = BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;

// We assume that a log entry data block can't be more than 9_999_999 bytes long, so
// we allocate up to 7 characters for this to be printed in decimal in the HTTP header.
// static const size_t worst_case_data_length = 7;

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

// #define portable_assert(x) assert(x)

const uint16_t sbb_log_port_number = 8066;

//////////////////////////////
// Exported function bodies //
//////////////////////////////

#ifdef NETWORK_LOGS
void Log_Net_Initialize()
{
    // On POSIX, implementation is null
    return;
}

// Send network logs in simulation as well
void Log_Net_Send(uint8_t *Transmit_Buffer, size_t total)
{
      // POSIX-specific implementation of socket handling code
      int sockfd;
      int bytes, sent;
      char *host = "localhost";
      struct hostent *server;
      struct sockaddr_in serv_addr;
      printf("port_number=%hu\n", sbb_log_port_number);

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
      serv_addr.sin_port = htons(sbb_log_port_number);
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

}
#else // NETWORK_LOGS

void Log_Net_Initialize(void) { return; }

void Log_Net_Send(uint8_t *Transmit_Buffer, size_t total) {
  (void) Transmit_Buffer;
  (void) total;
}
#endif //NETWORK_LOGS
