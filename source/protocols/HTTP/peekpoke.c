/*
 * peekpoke.c -- the meat of our "simple" peek and poke web server
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS Protocol includes. */
#include "FreeRTOS_HTTP_commands.h"
#include "FreeRTOS_TCP_server.h"
#include "FreeRTOS_server_private.h"

/* Specifics for the peekpoke server. */
#include "peekpoke.h"

/* First, some helper functions. */

static char *addressToCharPtr( long long int address )
{
    /* convert first to unsigned 32-bit int */
    unsigned int tmp = address & 0xffffffff;
    return (char *) tmp; /* evil! */
}

static void *addressToVoidPtr( long long int address )
{
    /* convert first to unsigned 32-bit int */
    unsigned int tmp = address & 0xffffffff;
    return (void *) tmp; /* evil! */
}

/* and the malware function */

static size_t malware(__attribute__((unused)) void *the_ptr,
                      __attribute__((unused)) size_t the_int)
{
    // need to make this take up some specific amount of memory
    // using either inline assembly or some other trickery
    return 0;
}

/* Stateful functions to split a slash-separated string of numbers. */

static const char *urlBuf = NULL;
static const char *otherData = NULL;
static int endOfHeadersSeen = 0;

/*
 * Initializes our hacky HTTP request processor with the URL and
 * the "other data" (basically, everything starting with "HTTP/1.1"
 * and heading into the headers and, if present, message body.
 */
static void loadRequestData(const char* urlBuf_, const char* otherData_)
{
    urlBuf = urlBuf_;
    otherData = otherData_;
    endOfHeadersSeen = 0;
}

/*
 * Given a URL containing slash-separated numeric strings, returns
 * the next number and advances further into the URL.
 */
static long long int getNextNumberFromURL(void)
{
    /* 
     * Infinite list of todo items that will never happen here:
     * - Unicode support
     * - Error handling for non-integer inputs
     * - Integers that are too big, so have overflows/wraparounds
     */

    if ( urlBuf == NULL )
    {
        return 0;
    }

    char *endPtr = NULL;
    long long int result = strtoll(urlBuf, &endPtr, 0); // overwrites endPtr

    if ( endPtr == NULL )
    {
        urlBuf = NULL;
    }
    else if ( *endPtr == '/' )
    {
        /*
         * This is the desired state: the first "invalid" character
         * is the slash character, so we'll start again next time one
         * character beyond it. 
         */
        urlBuf = endPtr + 1;
    }
    else if ( endPtr == urlBuf ) {
        /* No valid number found at all! Note absence of error handling. */
        urlBuf = NULL;
        result = 0;
    }
    else
    {
        /* Probably at the 0-terminated end of the string, i.e, *endPtr = 0 */
        urlBuf = endPtr;
    }

    return result;
}

#define BUF_SIZE 1024
static char outputBuf[BUF_SIZE]; /* worries about buffer overflows here? ha! */

/*
 * Returns string for the header line, with the customary termination (\r\n)
 * removed. The same internal buffer is used every time, so make a copy if
 * you need it. Returns NULL when the headers are done.
 */
static char* getNextHttpHeader( void )
{
    if ( endOfHeadersSeen ) return NULL;
    
    char* next = outputBuf;
    for (;;)
    {
        switch ( *otherData )
        {
        case '\0':
            // FreeRTOS_debug_printf(("0-char found, end of input\r\n"));
            endOfHeadersSeen = 1;
            return outputBuf;
        case '\r':
            // FreeRTOS_debug_printf(("carriage-return found\r\n"));
            if ( otherData[1] == '\n' )
            {
                // FreeRTOS_debug_printf(("newline found\r\n"));
                otherData = otherData + 2; // skip over \r\n
                *next = '\0';
                if ( next == outputBuf ) // blank line, end of headers
                {
                    // FreeRTOS_debug_printf(("blank line found, end of input\r\n"));
                    endOfHeadersSeen = 1;
                    return NULL;
                }
                return outputBuf;
            }
            // fallthrough
        default:
            *next = otherData[0];
            next++;
            otherData++;
        }
    }
}

static const char* getHttpBody( void )
{
    char* header;
    
    while ( (header = getNextHttpHeader() ) != NULL )
    {
        FreeRTOS_debug_printf(("Skipping header: %s\r\n", header));
    }
    return otherData;
}

static char heapBuffer[BUF_SIZE] = "plugh";

size_t peekPokeHandler( HTTPClient_t *pxClient, BaseType_t xIndex, const char *pcURLData, char *pcOutputBuffer, size_t uxBufferLength )
{
    char stackBuffer[BUF_SIZE] = "xyzzy";
    
    switch ( xIndex )
    {
    case ECMD_GET:
        // could be "/hello" or "/peek/address/length" or "/run/pointer/integer"
        if ( 0 == strncmp( "/hello", pcURLData, 6 ) )
        {
            strcpy( pxClient->pxParent->pcContentsType, "text/plain" );

            /* useful for a hacker to have a stack addr */
            snprintf( pcOutputBuffer, uxBufferLength,
                      "It's dark here; you may be eaten by a grue.\n\n&stackBuffer = %p\n&heapBuffer = %p\nBUF_SIZE = %d\nuxBufferLength = %d\nstackBuffer = %s\nheapBuffer = %s\n",
                      &stackBuffer, &heapBuffer, BUF_SIZE, uxBufferLength, stackBuffer, heapBuffer );


            /* all this print logging to help debug the HTTP header processing */

            FreeRTOS_debug_printf(("GET %s\r\n", pcURLData));

            char *tmp;
            while ( (tmp = getNextHttpHeader()) != NULL )
            {
                FreeRTOS_debug_printf(("==> %s\r\n", tmp));
            }

            FreeRTOS_debug_printf(("BODY\r\n%s", getHttpBody()));

            return strlen( pcOutputBuffer );
        }
        else if ( 0 == strncmp( "/peek/", pcURLData, 6 ) )
        {
            strcpy( pxClient->pxParent->pcContentsType, "application/octet-stream" );

            loadRequestData(pcURLData + 6, pxClient->pcRestData);
            long long int memAddress = getNextNumberFromURL();
            size_t readLength = getNextNumberFromURL();
            const char *mem = addressToCharPtr( memAddress );

            if ( memAddress != 0 && readLength != 0 )
            {
                if ( readLength > uxBufferLength )
                {
                    readLength = uxBufferLength; /* best we can do */
                }

                bzero( pcOutputBuffer, uxBufferLength ); 
                memcpy( pcOutputBuffer, mem, readLength ); /* evil! */

                return readLength;
            }
        }
        else if ( 0 == strncmp( "/run/", pcURLData, 5 ) )
        {
            strcpy( pxClient->pxParent->pcContentsType, "application/octet-stream" );

            loadRequestData(pcURLData + 5, pxClient->pcRestData);
            long long int malware_pointer_address = getNextNumberFromURL();
            size_t malware_int = getNextNumberFromURL();
            void *malware_pointer = addressToVoidPtr( malware_pointer_address );

            // execute the malware function with the specified parameters
            return malware(malware_pointer, malware_int);
        }
        break;
    case ECMD_PATCH:
        // could be "/poke/address/length" with body having attack bytes
        if ( 0 == strncmp( "/poke/", pcURLData, 6 ) ) {
            strcpy( pxClient->pxParent->pcContentsType, "text/plain" );

            loadRequestData(pcURLData + 6, pxClient->pcRestData);
            
            int memAddress = getNextNumberFromURL();
            int writeLength = getNextNumberFromURL();
            char *mem = addressToCharPtr( memAddress );

            // need to change this guard such that it only allows
            // poking into the malware function body
            if ( memAddress != 0 && writeLength != 0 )
            {
                memcpy( mem, getHttpBody(), writeLength ); /* evil! */
                snprintf( pcOutputBuffer, uxBufferLength,
                          "Wrote %d bytes to %p for 'ya!\n", writeLength, mem );
            }
            else
            {
                snprintf( pcOutputBuffer, uxBufferLength,
                          "Couldn't write that amount of data to that address!\n");
            }

            return strlen( pcOutputBuffer );
        }
        break;
    default:
        break;
    }

    /* if there's an error */
    strcpy( pxClient->pxParent->pcContentsType, "text/plain" );
    snprintf( pcOutputBuffer, uxBufferLength, "Sorry, don't understand that.\n" );
    return strlen( pcOutputBuffer );
}

static TaskHandle_t xWebServerTaskHandle = NULL; /* written by xTaskCreate() */

static void prvWebServerTask( void *pvParameters )
{
    TCPServer_t *pxTCPServer = NULL;
    const TickType_t xInitialBlockTime = pdMS_TO_TICKS( 5000UL );

    /* A structure that defines the servers to be created.  Which servers are
       included in the structure depends on the mainCREATE_HTTP_SERVER and
       mainCREATE_FTP_SERVER settings at the top of this file. */
    static const struct xSERVER_CONFIG xServerConfiguration[] =
        {
            /* Server type,     port number,    backlog,    root dir. */
            { eSERVER_HTTP,     80,             12,         "" },
        };


    /* Remove compiler warning about unused parameter. */
    ( void ) pvParameters;

    FreeRTOS_debug_printf(("prvWebServerTask: Making TCP server\r\n"));

    /* Wait until the network is up before creating the servers.  The
       notification is given from the network event hook. Currently
       disabled because we're doing the relevant logic in sbb_tcp.c */
    /* ulTaskNotifyTake( pdTRUE, portMAX_DELAY ); */

    /* Create the servers defined by the xServerConfiguration array above. */
    pxTCPServer = FreeRTOS_CreateTCPServer( xServerConfiguration, sizeof( xServerConfiguration ) / sizeof( xServerConfiguration[ 0 ] ) );
    configASSERT( pxTCPServer );

    for ( ;; )
    {
        /* Run the HTTP and/or FTP servers, as configured above. */
        FreeRTOS_TCPServerWork( pxTCPServer, xInitialBlockTime );
    }
}

#define mainTCP_SERVER_STACK_SIZE               ( configMINIMAL_STACK_SIZE * 8 )

static UBaseType_t savedPriority = 0;

void peekPokeServerTaskPriority( UBaseType_t uxPriority )
{
    savedPriority = uxPriority;
}

static int alreadyCreated = 0;

void peekPokeServerTaskCreate( void )
{
    if ( !alreadyCreated )  
    {
        alreadyCreated = 1;
        xTaskCreate( prvWebServerTask, "prvWebServerTask", mainTCP_SERVER_STACK_SIZE, NULL, savedPriority, &xWebServerTaskHandle );
    }
}
