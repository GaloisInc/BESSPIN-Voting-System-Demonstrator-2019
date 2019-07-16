/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */


/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>

/* FreeRTOS  includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "sbb.h"

/* IP stack includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/*
 * Just seeds the simple pseudo random number generator.
 */
static void prvSRand(UBaseType_t ulSeed);

/*
 * Miscellaneous initialisation including preparing the logging and seeding the
 * random number generator.
 */
static void prvMiscInitialisation(void);

uint32_t ulApplicationGetNextSequenceNumber(uint32_t ulSourceAddress,
											uint16_t usSourcePort,
											uint32_t ulDestinationAddress,
											uint16_t usDestinationPort);

/* The default IP and MAC address used by the demo.  The address configuration
defined here will be used if ipconfigUSE_DHCP is 0, or if ipconfigUSE_DHCP is
1 but a DHCP server could not be contacted.  See the online documentation for
more information. */
static const uint8_t ucIPAddress[4] = {configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3};
static const uint8_t ucNetMask[4] = {configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3};
static const uint8_t ucGatewayAddress[4] = {configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3};
static const uint8_t ucDNSServerAddress[4] = {configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3};

/* Set the following constant to pdTRUE to log using the method indicated by the
name of the constant, or pdFALSE to not log using the method indicated by the
name of the constant.  Options include to standard out (xLogToStdout), to a disk
file (xLogToFile), and to a UDP port (xLogToUDP).  If xLogToUDP is set to pdTRUE
then UDP messages are sent to the IP address configured as the echo server
address (see the configECHO_SERVER_ADDR0 definitions in FreeRTOSConfig.h) and
the port number set by configPRINT_PORT in FreeRTOSConfig.h. */
const BaseType_t xLogToStdout = pdTRUE, xLogToFile = pdFALSE, xLogToUDP = pdFALSE;

/* Default MAC address configuration.  The demo creates a virtual network
connection that uses this MAC address by accessing the raw Ethernet data
to and from a real network connection on the host PC.  See the
configNETWORK_INTERFACE_TO_USE definition for information on how to configure
the real network connection to use. */
const uint8_t ucMACAddress[6] = {configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5};
/*-----------------------------------------------------------*/

bool the_network_status = false;
void sbb_tcp(void);
void reportIPStatus(void);

/*-----------------------------------------------------------*/

void sbb_tcp(void)
{
	/* Miscellaneous initialisation including preparing the logging and seeding
	the random number generator. */
	prvMiscInitialisation();

	/* Initialise the network interface.
	***NOTE*** Tasks that use the network are created in the network event hook
	when the network is connected and ready for use (see the definition of
	vApplicationIPNetworkEventHook() below).  The address values passed in here
	are used if ipconfigUSE_DHCP is set to 0, or if ipconfigUSE_DHCP is set to 1
	but a DHCP server cannot be	contacted. */
	FreeRTOS_debug_printf(("FreeRTOS_IPInit\r\n"));
	FreeRTOS_IPInit(ucIPAddress, ucNetMask, ucGatewayAddress, ucDNSServerAddress, ucMACAddress);
}
/*-----------------------------------------------------------*/

/* Called by FreeRTOS+TCP when the network connects or disconnects.  Disconnect
events are only received if implemented in the MAC driver. */
void vApplicationIPNetworkEventHook(eIPCallbackEvent_t eNetworkEvent)
{
	uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
	char cBuffer[16];
	static BaseType_t xTasksAlreadyCreated = pdFALSE;

	/* If the network has just come up...*/
	if (eNetworkEvent == eNetworkUp)
	{
		the_network_status = true;
		/* Create the tasks that use the IP stack if they have not already been
		created. */
		if (xTasksAlreadyCreated == pdFALSE)
		{
			xTasksAlreadyCreated = pdTRUE;
		}

		/* Print out the network configuration, which may have come from a DHCP
		server. */
		FreeRTOS_GetAddressConfiguration(&ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress);
		FreeRTOS_inet_ntoa(ulIPAddress, cBuffer);
		FreeRTOS_printf(("\r\n\r\nIP Address: %s\r\n", cBuffer));

		FreeRTOS_inet_ntoa(ulNetMask, cBuffer);
		FreeRTOS_printf(("Subnet Mask: %s\r\n", cBuffer));

		FreeRTOS_inet_ntoa(ulGatewayAddress, cBuffer);
		FreeRTOS_printf(("Gateway Address: %s\r\n", cBuffer));

		FreeRTOS_inet_ntoa(ulDNSServerAddress, cBuffer);
		FreeRTOS_printf(("DNS Server Address: %s\r\n\r\n\r\n", cBuffer));
	}
	else
	{
        the_network_status = false;
	}
}
/*-----------------------------------------------------------*/

static void prvSRand(UBaseType_t ulSeed)
{
	/* Utility function to seed the pseudo random number generator. */
	ulNextRand = ulSeed;
}
/*-----------------------------------------------------------*/

static void prvMiscInitialisation(void)
{
	uint32_t seed = 42;
	FreeRTOS_debug_printf(("Seed for randomiser: %lu\r\n", seed));
	prvSRand((uint32_t)seed);
	FreeRTOS_debug_printf(("Random numbers: %08lX %08lX %08lX %08lX\r\n", ipconfigRAND32(), ipconfigRAND32(), ipconfigRAND32(), ipconfigRAND32()));
}
/*-----------------------------------------------------------*/

#if (ipconfigUSE_LLMNR != 0) || (ipconfigUSE_NBNS != 0) || (ipconfigDHCP_REGISTER_HOSTNAME == 1)

const char *pcApplicationHostnameHook(void)
{
	/* Assign the name "FreeRTOS" to this network node.  This function will
		be called during the DHCP: the machine will be registered with an IP
		address plus this name. */
	return mainHOST_NAME;
}

#endif
/*-----------------------------------------------------------*/

#if (ipconfigUSE_LLMNR != 0) || (ipconfigUSE_NBNS != 0)

BaseType_t xApplicationDNSQueryHook(const char *pcName)
{
	BaseType_t xReturn;

	/* Determine if a name lookup is for this node.  Two names are given
		to this node: that returned by pcApplicationHostnameHook() and that set
		by mainDEVICE_NICK_NAME. */
	if (_stricmp(pcName, pcApplicationHostnameHook()) == 0)
	{
		xReturn = pdPASS;
	}
	else if (_stricmp(pcName, mainDEVICE_NICK_NAME) == 0)
	{
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}

#endif

/*
 * Callback that provides the inputs necessary to generate a randomized TCP
 * Initial Sequence Number per RFC 6528.  THIS IS ONLY A DUMMY IMPLEMENTATION
 * THAT RETURNS A PSEUDO RANDOM NUMBER SO IS NOT INTENDED FOR USE IN PRODUCTION
 * SYSTEMS.
 */
uint32_t ulApplicationGetNextSequenceNumber(uint32_t ulSourceAddress,
											uint16_t usSourcePort,
											uint32_t ulDestinationAddress,
											uint16_t usDestinationPort)
{
	(void)ulSourceAddress;
	(void)usSourcePort;
	(void)ulDestinationAddress;
	(void)usDestinationPort;

	return uxRand();
}

//
void reportIPStatus(void)
{
	uint32_t ulIPAddress, ulNetMask, ulGatewayAddress, ulDNSServerAddress;
	char cBuffer[16];

	/* Print out the network configuration, which may have come from a DHCP
	   server. */
	FreeRTOS_GetAddressConfiguration(&ulIPAddress, &ulNetMask, &ulGatewayAddress, &ulDNSServerAddress);
	FreeRTOS_inet_ntoa(ulIPAddress, cBuffer);
	FreeRTOS_printf(("\r\n\r\nIP Address: %s\r\n", cBuffer));

	FreeRTOS_inet_ntoa(ulNetMask, cBuffer);
	FreeRTOS_printf(("Subnet Mask: %s\r\n", cBuffer));

	FreeRTOS_inet_ntoa(ulGatewayAddress, cBuffer);
	FreeRTOS_printf(("Gateway Address: %s\r\n", cBuffer));

	FreeRTOS_inet_ntoa(ulDNSServerAddress, cBuffer);
	FreeRTOS_printf(("DNS Server Address: %s\r\n\r\n\r\n", cBuffer));
}
