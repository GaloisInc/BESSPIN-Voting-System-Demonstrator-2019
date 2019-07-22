/*
 * FreeRTOS+TCP Labs Build 160919 (C) 2016 Real Time Engineers ltd.
 * Authors include Hein Tibosch and Richard Barry
 *
 *******************************************************************************
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 ***                                                                         ***
 ***                                                                         ***
 ***   FREERTOS+TCP IS STILL IN THE LAB (mainly because the FTP and HTTP     ***
 ***   demos have a dependency on FreeRTOS+FAT, which is only in the Labs    ***
 ***   download):                                                            ***
 ***                                                                         ***
 ***   FreeRTOS+TCP is functional and has been used in commercial products   ***
 ***   for some time.  Be aware however that we are still refining its       ***
 ***   design, the source code does not yet quite conform to the strict      ***
 ***   coding and style standards mandated by Real Time Engineers ltd., and  ***
 ***   the documentation and testing is not necessarily complete.            ***
 ***                                                                         ***
 ***   PLEASE REPORT EXPERIENCES USING THE SUPPORT RESOURCES FOUND ON THE    ***
 ***   URL: http://www.FreeRTOS.org/contact  Active early adopters may, at   ***
 ***   the sole discretion of Real Time Engineers Ltd., be offered versions  ***
 ***   under a license other than that described below.                      ***
 ***                                                                         ***
 ***                                                                         ***
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 *******************************************************************************
 *
 * FreeRTOS+TCP can be used under two different free open source licenses.  The
 * license that applies is dependent on the processor on which FreeRTOS+TCP is
 * executed, as follows:
 *
 * If FreeRTOS+TCP is executed on one of the processors listed under the Special
 * License Arrangements heading of the FreeRTOS+TCP license information web
 * page, then it can be used under the terms of the FreeRTOS Open Source
 * License.  If FreeRTOS+TCP is used on any other processor, then it can be used
 * under the terms of the GNU General Public License V2.  Links to the relevant
 * licenses follow:
 *
 * The FreeRTOS+TCP License Information Page: http://www.FreeRTOS.org/tcp_license
 * The FreeRTOS Open Source License: http://www.FreeRTOS.org/license
 * The GNU General Public License Version 2: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * FreeRTOS+TCP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+TCP unless you agree that you use the software 'as is'.
 * FreeRTOS+TCP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/plus
 * http://www.FreeRTOS.org/labs
 *
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

/* FreeRTOS+FAT includes. */
// #include "ff_stdio.h"

/* Specifics for the peekpoke server. */
#include "peekpoke.h"

#ifndef HTTP_SERVER_BACKLOG
	#define HTTP_SERVER_BACKLOG			( 12 )
#endif

#ifndef USE_HTML_CHUNKS
	#define USE_HTML_CHUNKS				( 0 )
#endif

#if !defined( ARRAY_SIZE )
	#define ARRAY_SIZE(x) ( BaseType_t ) (sizeof( x ) / sizeof( x )[ 0 ] )
#endif

/* Some defines to make the code more readbale */
#define pcCOMMAND_BUFFER	pxClient->pxParent->pcCommandBuffer
#define pcNEW_DIR			pxClient->pxParent->pcNewDir
#define pcFILE_BUFFER		pxClient->pxParent->pcFileBuffer

#ifndef ipconfigHTTP_REQUEST_CHARACTER
	#define ipconfigHTTP_REQUEST_CHARACTER		'?'
#endif

/*_RB_ Need comment block, although fairly self evident. */
static BaseType_t prvOpenURL( HTTPClient_t *pxClient, BaseType_t xIndex );
static BaseType_t prvSendReply( HTTPClient_t *pxClient, BaseType_t xCode );

static const char pcEmptyString[1] = { '\0' };

typedef struct xTYPE_COUPLE
{
	const char *pcExtension;
	const char *pcType;
} TypeCouple_t;

static BaseType_t prvSendReply( HTTPClient_t *pxClient, BaseType_t xCode )
{
	struct xTCP_SERVER *pxParent = pxClient->pxParent;
	BaseType_t xRc;

	/* A normal command reply on the main socket (port 21). */
	char *pcBuffer = pxParent->pcFileBuffer;

	xRc = snprintf( pcBuffer, sizeof( pxParent->pcFileBuffer ),
					"HTTP/1.1 %d %s\r\n"
#if	USE_HTML_CHUNKS
					"Transfer-Encoding: chunked\r\n"
#endif
					"Content-Type: %s\r\n"
					"Connection: keep-alive\r\n"
					"%s\r\n",
					( int ) xCode,
					webCodename (xCode),
					pxParent->pcContentsType[0] ? pxParent->pcContentsType : "text/html",
					pxParent->pcExtraContents );

	pxParent->pcContentsType[0] = '\0';
	pxParent->pcExtraContents[0] = '\0';

	xRc = FreeRTOS_send( pxClient->xSocket, ( const void * ) pcBuffer, xRc, 0 );
	pxClient->bits.bReplySent = pdTRUE_UNSIGNED;

	return xRc;
}

/*-----------------------------------------------------------*/

static BaseType_t prvOpenURL( HTTPClient_t *pxClient, BaseType_t xIndex )
{
	BaseType_t xRc;

	pxClient->bits.ulFlags = 0;

	FreeRTOS_debug_printf(("OpenURL: %s\r\n", pxClient->pcUrlData));

	size_t xResult = peekPokeHandler( pxClient,
									  xIndex,
									  pxClient->pcUrlData,
									  pxClient->pcCurrentFilename,
									  sizeof( pxClient->pcCurrentFilename ) );

	if( xResult > 0 )
	{
		FreeRTOS_debug_printf(("Successful handler: %d bytes\r\n", xResult));

		snprintf( pxClient->pxParent->pcExtraContents, sizeof( pxClient->pxParent->pcExtraContents ),
				  "Content-Length: %d\r\n", ( int ) xResult );
		xRc = prvSendReply( pxClient, WEB_REPLY_OK );	/* "Requested file action OK" */
		if( xRc > 0 )
		{
			xRc = FreeRTOS_send( pxClient->xSocket, pxClient->pcCurrentFilename, xResult, 0 );
			if( xRc <= 0 )
			{
				FreeRTOS_debug_printf(("Error returned from FreeRTOS_send: %ld\r\n", xRc));
			}
		}
		else
		{
			FreeRTOS_debug_printf(("Error returned from prvSendReply: %ld\r\n", xRc));
		}
	}
	else
	{
		FreeRTOS_debug_printf(("Error in peekPokeHandler: %d\r\n", xResult));

		/* "404 File not found". */
		xRc = prvSendReply( pxClient, WEB_NOT_FOUND );
		if( xRc <= 0 )
		{
			FreeRTOS_debug_printf(("Error in prvSendReply for 404 not found: %ld\r\n", xRc));
		}
	}

	return xRc;
}

BaseType_t xHTTPClientWork( TCPClient_t *pxTCPClient )
{
	BaseType_t xRc;
	HTTPClient_t *pxClient = ( HTTPClient_t * ) pxTCPClient;

	xRc = FreeRTOS_recv( pxClient->xSocket, ( void * )pcCOMMAND_BUFFER, sizeof( pcCOMMAND_BUFFER ), 0 );

	if( xRc > 0 )
	{
		BaseType_t xIndex;
		const char *pcEndOfCmd;
		const struct xWEB_COMMAND *curCmd;
		char *pcBuffer = pcCOMMAND_BUFFER;

		if( xRc < ( BaseType_t ) sizeof( pcCOMMAND_BUFFER ) )
		{
			pcBuffer[ xRc ] = '\0';
		}
		while( xRc && ( pcBuffer[ xRc - 1 ] == 13 || pcBuffer[ xRc - 1 ] == 10 ) )
		{
			pcBuffer[ --xRc ] = '\0';
		}
		pcEndOfCmd = pcBuffer + xRc;

		curCmd = xWebCommands;

		/* Pointing to "/index.html HTTP/1.1". */
		pxClient->pcUrlData = pcBuffer;

		/* Pointing to "HTTP/1.1", after the for-loop below is done. */
		pxClient->pcRestData = pcEmptyString;

		for( xIndex = 0; xIndex < WEB_CMD_COUNT - 1; xIndex++, curCmd++ )
		{
			BaseType_t xLength;

			/* Comparing the command ("GET", "PUT", etc.) against known good commands. */
			xLength = curCmd->xCommandLength;
			if( ( xRc >= xLength ) && ( memcmp( curCmd->pcCommandName, pcBuffer, xLength ) == 0 ) )
			{
				char *pcLastPtr;

				/* URL is one character after the end of the command. */
				pxClient->pcUrlData += xLength + 1;
				for( pcLastPtr = (char *)pxClient->pcUrlData; pcLastPtr < pcEndOfCmd; pcLastPtr++ )
				{
					char ch = *pcLastPtr;

					/*
					 * If we find whitespace, or end of string, write out a
					 * string terminator, then save the rest of the data,
					 * which is to say, the stuff starting with "HTTP/1.1",
					 * the rest of the HTTP headers, and if present the HTTP
					 * body.
					 */
					if( ( ch == '\0' ) || ( strchr( "\n\r \t", ch ) != NULL ) )
					{
						*pcLastPtr = '\0';
						pxClient->pcRestData = pcLastPtr + 1;
						break;
					}
				}
				break;
			}
		}

		/* 
		 * TODO: skip pcRestData past the "HTTP/1.1" part all the way to the
		 * payload for a POST or PATCH command.
		 */

		if( xIndex < ( WEB_CMD_COUNT - 1 ) )
		{
			xRc = prvOpenURL( pxClient, xIndex );
		}
		else
		{
			FreeRTOS_printf( ( "unknown xIndex (%ld), not running prvOpenURL\r\n", xIndex ) );
		}
	}
	else if( xRc < 0 )
	{
		/* The connection will be closed and the client will be deleted. */
		FreeRTOS_printf( ( "xHTTPClientWork: rc = %ld\r\n", xRc ) );
	}
	return xRc;
}
