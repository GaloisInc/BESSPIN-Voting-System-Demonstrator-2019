#ifndef __LOG_NET_H__
#define __LOG_NET_H__


#ifdef TARGET_OS_FreeRTOS

/* FreeRTOS  includes. */
#include "FreeRTOS.h"

/* IP stack includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

// dragan values needs to be changed

// ucIPAddress
#define configIP_ADDR0	        10
#define configIP_ADDR1	        6
#define configIP_ADDR2	        6
#define configIP_ADDR3	        253

// ucNetMask
#define configNET_MASK0	        255
#define configNET_MASK1	        255
#define configNET_MASK2	        255
#define configNET_MASK3	        0

// ucGatewayAddress
#define configGATEWAY_ADDR0	    10
#define configGATEWAY_ADDR1	    10
#define configGATEWAY_ADDR2	    10
#define configGATEWAY_ADDR3	    1

// ucDNSServerAddress
#define configDNS_SERVER_ADDR0 	4
#define configDNS_SERVER_ADDR1 	2
#define configDNS_SERVER_ADDR2 	2
#define configDNS_SERVER_ADDR3 	2

// ucMACAddress 
#define configMAC_ADDR0	0x00
#define configMAC_ADDR1	0x12
#define configMAC_ADDR2	0x13
#define configMAC_ADDR3	0x10
#define configMAC_ADDR4	0x15
#define configMAC_ADDR5	0x11

static const uint8_t ucIPAddress[4] = {configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3};
static const uint8_t ucNetMask[4] = {configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3};
static const uint8_t ucGatewayAddress[4] = {configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3};
static const uint8_t ucDNSServerAddress[4] = {configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3};
const uint8_t ucMACAddress[6] = {configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5};


typedef struct Log_Handles
{
    FIL the_file;
    sha256_digest previous_hash; // This should really be in secure_log
} Log_Handle;

#else
// @assume We have a POSIX I/O filesystem.
#include <stdio.h> /* printf, sprintf */
#include <stdlib.h> /* exit */
#include <unistd.h> /* read, write, close */
#include <string.h> /* memcpy, memset */
#include <sys/socket.h> /* socket, connect */
#include <netinet/in.h> /* struct sockaddr_in, struct sockaddr */
#include <netdb.h> /* struct hostent, gethostbyname */


typedef struct Log_Handles
{
    FILE the_file;
    sha256_digest previous_hash;
} Log_Handle;
#endif

typedef Log_Handle *log_file;
typedef Log_Handle *log_io_stream;


void Log_NET_Initialize(ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress);

void Log_NET_Send(Log_Handle *stream, const size_t xTotalLengthToSend);



#endif /* __LOG_IO_H__ */
