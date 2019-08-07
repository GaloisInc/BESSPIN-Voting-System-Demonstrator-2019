/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */
#ifndef __SBB_FREERTOS_H__
#define __SBB_FREERTOS_H__

//#include "sbb.h"
#include "sbb_io_constants.h"
#include "sbb_t.h"

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* FreeRTOS includes */
#include "event_groups.h"
#include "stream_buffer.h"

void prvBallotBoxMainTask(void *pvParameters);
void prvBarcodeScannerTask(void *pvParameters);
void prvInputTask(void *pvParameters);
void prvNetworkLogTask(void *pvParameters);
void prvStartupTask(void *pvParameters);
void prvMalwareTask(void *pvParameters);

void sbb_tcp(void);
void reportIPStatus(void);

extern StreamBufferHandle_t xNetLogStreamBuffer;
extern StreamBufferHandle_t xScannerStreamBuffer;
extern EventGroupHandle_t xSBBEventGroup;

extern TaskHandle_t prvStartupTaskHandle;

/* Smart Ballot Box Tasks and priorities*/
#define SBB_MAIN_TASK_PRIORITY tskIDLE_PRIORITY + 1
#define SBB_SCANNER_TASK_PRIORITY tskIDLE_PRIORITY + 2
#define SBB_INPUT_TASK_PRIORITY tskIDLE_PRIORITY + 3
#define SBB_NET_LOG_TASK_PRIORITY tskIDLE_PRIORITY + 3
#define SBB_STARTUP_TASK_PRIORITY tskIDLE_PRIORITY
#define SBB_PEEKPOKE_TASK_PRIORITY tskIDLE_PRIORITY + 2
#define SBB_STATS_TASK_PRIORITY tskIDLE_PRIORITY + 1

#define SBB_MAIN_TASK_STACK_SIZE configMINIMAL_STACK_SIZE * 10U
#define SBB_SCANNER_TASK_STACK_SIZE configMINIMAL_STACK_SIZE * 10U
#define SBB_INPUT_TASK_STACK_SIZE configMINIMAL_STACK_SIZE * 10U
#define SBB_NET_LOG_TASK_STACK_SIZE configMINIMAL_STACK_SIZE * 10U
#define SBB_STARTUP_TASK_STACK_SIZE configMINIMAL_STACK_SIZE * 10U

#define sbLOG_BUFFER_SIZE 2048
#define sbLOG_BUFFER_TRIGGER_LEVEL 331

/* The number of bytes of storage in the stream buffers */
#define sbSTREAM_BUFFER_LENGTH_BYTES ((size_t)BARCODE_MAX_LENGTH)
/* The trigger level sets the number of bytes that must be present in the
   stream buffer before a task that is blocked on the stream buffer is moved out of
   the Blocked state so it can read the bytes. */
#define sbTRIGGER_LEVEL_1 (1)
/* How long we wait to send scanned barcode */
#define SCANNER_BUFFER_TX_BLOCK_TIME_MS pdMS_TO_TICKS(15)
/* How long we wait to receive a scanned barcode */
#define SCANNER_BUFFER_RX_BLOCK_TIME_MS pdMS_TO_TICKS(15)
/* How long to wait before we "see" a paper sensor "release" */
#define PAPER_SENSOR_DEBOUNCE pdMS_TO_TICKS(1500)

/* Event bit definitions. */
#define ebPAPER_SENSOR_IN_PRESSED (0x01)
#define ebPAPER_SENSOR_IN_RELEASED (0x02)
#define ebBARCODE_SCANNED (0x04)
#define ebCAST_BUTTON_PRESSED (0x08)
#define ebCAST_BUTTON_RELEASED (0x10)
#define ebSPOIL_BUTTON_PRESSED (0x20)
#define ebSPOIL_BUTTON_RELEASED (0x40)
#define ebALL_EVENTS (0x7F)

#define ebALL_PAPER_SENSOR_EVENTS                                              \
    (ebPAPER_SENSOR_IN_PRESSED | ebPAPER_SENSOR_IN_RELEASED)

#define ebALL_BUTTON_EVENTS                                                    \
    (ebCAST_BUTTON_RELEASED | ebCAST_BUTTON_PRESSED |                          \
     ebSPOIL_BUTTON_RELEASED | ebSPOIL_BUTTON_PRESSED)

/* Input defines */
#define GPIO_READ_DELAY_MS pdMS_TO_TICKS(100)

/*
 * Just seeds the simple pseudo random number generator.
 */
void prvSRand(UBaseType_t ulSeed);

#ifdef SIMULATION
/*
 * Functions broadcasting various events 
 */
void sim_paper_sensor_in_pressed(void);
void sim_paper_sensor_in_released(void);
void sim_valid_barcode_scanned(uint8_t id);
void sim_cast_button_pressed(void);
void sim_spoil_button_pressed(void);

#ifdef SIMULATION_UART
#define SIM_COMMAND_BUFFER_LENGTH 17
#define SIM_BARCODE_BUFFER_LENGTH 384
/*
 * Main UART simulator loop and barcode input function
 */
void sim_uart_main_loop(void);
void sim_barcode_input(void);
#endif // SIMULATION_UART
#endif // SIMULATION

#endif /* __SBB_FREERTOS_H__ */
