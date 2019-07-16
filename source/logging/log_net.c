///////////////////////////////////////////////////////
// Common include files needed by all implemenations //
///////////////////////////////////////////////////////

#include "log_net.h"
#include "../crypto/crypto.h"
#include "debug_io.h"
#include "log_io.h"

#include <stdio.h>

///////////////////////////////////////////////////
// Common constants needed by all implemenations //
///////////////////////////////////////////////////

static const char space = ' ';
static const char new_line = '\n';

static const char *REQUEST_LINE_1 = "POST /";
static const char *REQUEST_LINE_3 = " HTTP/1.1\r\n";
static const char *HEADER_1 = "Host: 10.5.5.1\r\n";
static const char *HEADER_2 = "User-Agent: sbb/2019\r\n";
static const char *HEADER_3 = "Accept: */*\r\n";
static const char *HEADER_4 = "Content-Type: application/octet-stream\r\n";
static const char *HEADER_5_1 = "Content-Length: ";
static const char *DOUBLE_CRLF = "\r\n\r\n";

//static const size_t data_block_length = BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;
static const uint16_t PORT_NUMBER = 8066;

// We assume that a log entry data block can't be more than 9_999_999 bytes long, so
// we allocate up to 7 characters for this to be printed in decimal in the HTTP header.
// static const size_t worst_case_data_length = 7;

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
//static const uint8_t SBB_NetMask[4] = {255, 255, 255, 0};
//static const uint8_t SBB_GatewayAddress[4] = {10, 10, 10, 1};
//static const uint8_t SBB_DNSServerAddress[4] = {4, 2, 2, 2};
//static const uint8_t Reporting_Server_IP_Address[4] = {10, 6, 6, 253};

// Network configuration and addresses that will be different for each SBB

// RCC made this up - to be confirmed
// Should be different for each SBB
//static uint8_t This_SBB_IP_Address[4] = {10, 6, 6, 1};

// RCC No idea where these numbers came from - to be confirmed
// Should be different for each SBB
//static uint8_t This_SBB_MAC_Address[6] = {0x00, 0x12, 0x13, 0x10, 0x15, 0x11};

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

// #define portable_assert(x) assert(x)

#endif


//////////////////////////////
// Exported function bodies //
//////////////////////////////

#ifdef NETWORK_LOGS
void Log_Net_Initialize()
{
#ifdef TARGET_OS_FreeRTOS
<<<<<<< HEAD
  // On FreeRTOS, this is currently null.
  //
  // We assume that FreeRTOS_IPInit() has been called already
  // by the main program.

=======
    debug_printf("FreeRTOS_IPInit");
//    FreeRTOS_IPInit(This_SBB_IP_Address, SBB_NetMask, SBB_GatewayAddress,
//                    SBB_DNSServerAddress, This_SBB_MAC_Address);
>>>>>>> Turned on network logging and forced IP addresses for testing.
#endif
    // On POSIX, implementation is null
    return;
}


void Log_Net_Send(uint8_t *Transmit_Buffer, size_t total)
{
#ifdef SIMULATION
	return;
#endif
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
	      (configRptrIP_ADDR0, configRptrIP_ADDR1, configRptrIP_ADDR2, configRptrIP_ADDR3);
        //(Reporting_Server_IP_Address[0], Reporting_Server_IP_Address[1],
        // Reporting_Server_IP_Address[2], Reporting_Server_IP_Address[3]);

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
      printf("port_number=%hu\n", PORT_NUMBER);

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
#else // NETWORK_LOGS
// ACSL Contracts TBD
void Log_Net_Initialize(void) {}

// ACSL Contracts TBD
void Log_Net_Send(uint8_t *Transmit_Buffer, size_t total) {}
#endif //NETWORK_LOGS
