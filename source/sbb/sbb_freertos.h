/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */
#ifndef __SBB_FREERTOS_H__
#define __SBB_FREERTOS_H__

#include "sbb.h"

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* FreeRTOS includes */
#include "stream_buffer.h"
#include "event_groups.h"

extern StreamBufferHandle_t xScannerStreamBuffer;
extern EventGroupHandle_t xSBBEventGroup;

/* The number of bytes of storage in the stream buffers */
#define sbSTREAM_BUFFER_LENGTH_BYTES	( ( size_t ) BARCODE_MAX_LENGTH )
/* The trigger level sets the number of bytes that must be present in the
stream buffer before a task that is blocked on the stream buffer is moved out of
the Blocked state so it can read the bytes. */
#define sbTRIGGER_LEVEL_1			( 1 )
/* How long we wait to send scanned barcode */
#define SCANNER_BUFFER_TX_BLOCK_TIME_MS pdMS_TO_TICKS(5000)
/* How long we wait to receive a scanned barcode */
#define SCANNER_BUFFER_RX_BLOCK_TIME_MS pdMS_TO_TICKS(15)


/* Event bit definitions. */
#define ebPAPER_SENSOR_IN_PRESSED		( 0x01 )
#define ebPAPER_SENSOR_IN_RELEASED		( 0x02 )
#define ebPAPER_SENSOR_OUT_PRESSED		( 0x04 )
#define ebPAPER_SENSOR_OUT_RELEASED		( 0x08 )
#define ebBARCODE_SCANNED       		( 0x10 )
#define ebCAST_BUTTON_PRESSED	    	( 0x20 )
#define ebCAST_BUTTON_RELEASED	    	( 0x40 )
#define ebSPOIL_BUTTON_PRESSED	    	( 0x80 )
#define ebSPOIL_BUTTON_RELEASED		    ( 0x100 )

/* Input defines */
#define GPIO_READ_DELAY_MS pdMS_TO_TICKS(15)

#endif /* __SBB_FREERTOS_H__ */