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

/**
 * This is docs for main ballot box demo
 */

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* FreeRTOS includes */
#include "stream_buffer.h"
#include "event_groups.h"

/* Standard includes */ 
#include <stdio.h>
#include <string.h>
#include <stdbool.h>

/* Drivers */
#include "bsp.h"
#include "uart.h"
#include "gpio.h"
#include "ff.h" /* Declarations of FatFs API */
#include "diskio.h"

/* Smart Ballot Box includes */
#include "sbb.h"
#include "sbb_freertos.h"

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file.  See https://www.freertos.org/a00016.html */
void vApplicationMallocFailedHook(void);
void vApplicationIdleHook(void);
void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName);
void vApplicationTickHook(void);

/* Returns the current value of mcycle register*/
uint64_t get_cycle_count(void);

#if configGENERATE_RUN_TIME_STATS
/* Buffer and a task for displaying runtime stats */
char statsBuffer[1024];
static void prvStatsTask(void *pvParameters);
#endif /* configGENERATE_RUN_TIME_STATS */

/* Smart Ballot Box Tasks and priorities*/
#define SBB_MAIN_TASK_PRIORITY tskIDLE_PRIORITY+2
#define SBB_SCANNER_TASK_PRIORITY tskIDLE_PRIORITY+1
#define SBB_LOGGING_TASK_PRIORITY tskIDLE_PRIORITY+2
#define SBB_INPUT_TASK_PRIORITY tskIDLE_PRIORITY+3

static void prvBallotBoxMainTask(void *pvParameters);
static void prvBarcodeScannerTask(void *pvParameters);
static void prvLoggingTask(void *pvParameters);
static void prvInputTask(void *pvParameters);

/*-----------------------------------------------------------*/

StreamBufferHandle_t xScannerStreamBuffer;
EventGroupHandle_t xSBBEventGroup;

/*-----------------------------------------------------------*/

/**
 * Capture the current 64-bit cycle count.
 */
uint64_t get_cycle_count(void)
{
#if __riscv_xlen == 64
	return read_csr(mcycle);
#else
	uint32_t cycle_lo, cycle_hi;
	asm volatile(
		"%=:\n\t"
		"csrr %1, mcycleh\n\t"
		"csrr %0, mcycle\n\t"
		"csrr t1, mcycleh\n\t"
		"bne  %1, t1, %=b"
		: "=r"(cycle_lo), "=r"(cycle_hi)
		: // No inputs.
		: "t1");
	return (((uint64_t)cycle_hi) << 32) | (uint64_t)cycle_lo;
#endif
}

/**
 * Use `mcycle` counter to get usec resolution.
 * On RV32 only, reads of the mcycle CSR return the low 32 bits,
 * while reads of the mcycleh CSR return bits 63–32 of the corresponding
 * counter.
 * We convert the 64-bit read into usec. The counter overflows in roughly an hour
 * and 20 minutes. Probably not a big issue though.
 * At 50HMz clock rate, 1 us = 50 ticks
 */
uint32_t port_get_current_mtime(void)
{
	return (uint32_t)(get_cycle_count() / (configCPU_CLOCK_HZ / 1000000));
}

/**
 * Main application entry
 */
int main(void)
{
	prvSetupHardware();

	/* Initialize stream buffers */
	xScannerStreamBuffer = xStreamBufferCreate( sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1 );
	/* Initialize event groups */
	xSBBEventGroup = xEventGroupCreate();
	configASSERT( xSBBEventGroup );
	

	xTaskCreate(prvBallotBoxMainTask, "prvBallotBoxMainTask", configMINIMAL_STACK_SIZE * 2U, NULL, SBB_MAIN_TASK_PRIORITY, NULL);
	xTaskCreate(prvBarcodeScannerTask, "prvBarcodeScannerTask", configMINIMAL_STACK_SIZE * 2U, NULL, SBB_SCANNER_TASK_PRIORITY, NULL);
	//xTaskCreate(prvLoggingTask, "prvLoggingTask", configMINIMAL_STACK_SIZE * 2U, NULL, SBB_LOGGING_TASK_PRIORITY, NULL);
	xTaskCreate(prvInputTask, "prvInputTask", configMINIMAL_STACK_SIZE * 2U, NULL, SBB_INPUT_TASK_PRIORITY, NULL);

#if configGENERATE_RUN_TIME_STATS
	xTaskCreate(prvStatsTask, "prvStatsTask", configMINIMAL_STACK_SIZE * 2, NULL, tskIDLE_PRIORITY, NULL);
#endif

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the Idle and/or
	timer tasks to be created.  See the memory management section on the
	FreeRTOS web site for more details on the FreeRTOS heap
	http://www.freertos.org/a00111.html. */
	vTaskStartScheduler();
	for (;;)
		;
}
/*-----------------------------------------------------------*/

#if configGENERATE_RUN_TIME_STATS
static void prvStatsTask(void *pvParameters)
{
	(void)pvParameters;
	printf(("prvStatsTask: starting\r\n"));

	for (;;)
	{
		vTaskDelay(pdMS_TO_TICKS(10000));
		vTaskGetRunTimeStats(statsBuffer);
		printf("prvStatsTask: xPortGetFreeHeapSize() = %u\r\n", xPortGetFreeHeapSize());
		printf("prvStatsTask: Run-time stats\r\nTask\tAbsTime\tpercent_time\r\n");
		printf("%s\r\n", statsBuffer);
	}
}
#endif /* configGENERATE_RUN_TIME_STATS */

/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook(void)
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	__asm volatile("ebreak");
	for (;;)
		;
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook(void)
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName)
{
	(void)pcTaskName;
	(void)pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	__asm volatile("ebreak");
	for (;;)
		;
}
/*-----------------------------------------------------------*/

void vApplicationTickHook(void)
{
/* The tests in the full demo expect some interaction with interrupts. */
#if (mainDEMO_TYPE == 2)
	{
		extern void vFullDemoTickHook(void);
		vFullDemoTickHook();
	}
#endif
}
/*-----------------------------------------------------------*/


/**
 * Runs the main ballot box code
 */
static void prvBallotBoxMainTask(void *pvParameters)
{
	(void)pvParameters;
	printf("Starting prvBallotBoxMainTask\r\n");

	ballot_box_main_loop();
}
/*-----------------------------------------------------------*/

/**
 * Logs data onto the SD card
 */
static void prvLoggingTask(void *pvParameters)
{
	(void)pvParameters;
	FATFS FatFs; /* FatFs work area needed for each volume */
	FIL Fil;     /* File object needed for each open file */
	UINT bw;
	uint8_t res;

	printf("Starting prvLoggingTask\r\n");

	res = f_mount(&FatFs, "", 0);
    printf("f_mount result = %i\r\n", res); /* Give a work area to the default drive */

    if (!res) {
        if (f_open(&Fil, "log.txt", FA_WRITE | FA_CREATE_ALWAYS) == FR_OK) {	/* Create a new file */
            f_write(&Fil, "It works!\r\n", 11, &bw);	/* Write data to the file */
            f_close(&Fil);								/* Close the file */
            f_close(&Fil);								/* Close the file */
            if (bw == 11) {		/* was data written well */
                printf("data written sucessfully\r\n");
            } else {
                printf("data write error!\r\n");
            }
        } else {
            printf("f_mount error!\r\n");
        }
    }
    printf("prvSdTestTask0 terminating, exit code = %u\r\n", res);
}
/*-----------------------------------------------------------*/

/**
 * Aux task polling data from the barcode scanner
 */
static void prvBarcodeScannerTask(void *pvParameters)
{
	(void)pvParameters;

    uint8_t idx = 0;
	char barcode[BARCODE_MAX_LENGTH] = {0};

	printf("Starting prvBarcodeScannerTask\r\n");

    for (;;)
    {
        configASSERT(uart1_rxbuffer(&barcode[idx], 1) == 1);
        if (barcode[idx] == 0xd)
        {
			/* Debug print below */
			printf("Barcode, idx=%u: ", idx);
			for (uint8_t i=0;i<idx;i++) {
				printf("%c",barcode[i]);
			}
			printf("\r\n");
			/* We have a barcode, send it over stream buffer and fire the event */
			configASSERT( xStreamBufferSend( xScannerStreamBuffer, ( void * ) barcode, (size_t)idx, SCANNER_BUFFER_TX_BLOCK_TIME_MS ) == idx);
			/* Broadcast the event */
			configASSERT(xEventGroupSetBits( xSBBEventGroup, ebBARCODE_SCANNED ) & ebBARCODE_SCANNED);
			/* reset state */
			idx = 0;
			memset(barcode, 0, BARCODE_MAX_LENGTH);
        }
        else
        {
            idx++;
            if (idx >= BARCODE_MAX_LENGTH)
            {
				printf("Erasing idx\r\n");
                idx = 0;
            }
        }
        //vTaskDelay(pdMS_TO_TICKS(1));
    }
}

/*-----------------------------------------------------------*/

/* Task handling the GPIO inputs */
static void prvInputTask(void *pvParameters) {
	(void)pvParameters;
	EventBits_t uxReturned;

	printf("Starting prvInputTask\r\n");

	/* Buttons are active high */
    uint8_t cast_button_input = 0;
    uint8_t cast_button_input_last = 0;
	uint8_t spoil_button_input = 0;
    uint8_t spoil_button_input_last = 0;

	/* Sensors are active low */
	uint8_t paper_sensor_in_input = 1;
    uint8_t paper_sensor_in_input_last = 1;
	uint8_t paper_sensor_out_input = 1;
    uint8_t paper_sensor_out_input_last = 1;

	gpio_set_as_input(BUTTON_CAST_IN);
    gpio_set_as_input(BUTTON_SPOIL_IN);
    gpio_set_as_input(PAPER_SENSOR_IN);
    gpio_set_as_input(PAPER_SENSOR_OUT);

	for(;;) {
		/* Paper sensor in */
		paper_sensor_in_input = gpio_read(PAPER_SENSOR_IN);
		if (paper_sensor_in_input != paper_sensor_in_input_last) {
            printf("#paper_sensor_in_input changed: %u -> %u\r\n", paper_sensor_in_input_last, paper_sensor_in_input);
            
			/* Broadcast the event */
			if (paper_sensor_in_input == 0) {
				//configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED) & ebPAPER_SENSOR_IN_PRESSED);
				uxReturned = xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
				uxReturned = xEventGroupClearBits( xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
			} else {
				//configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED) & ebPAPER_SENSOR_IN_RELEASED);
				uxReturned = xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
				uxReturned = xEventGroupClearBits( xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
			}
			printf("uxReturned = 0x%lx\r\n",uxReturned);
			paper_sensor_in_input_last = paper_sensor_in_input;
        }

		/* Paper sensor out */
		paper_sensor_out_input = gpio_read(PAPER_SENSOR_OUT);
		if (paper_sensor_out_input != paper_sensor_out_input_last) {
            printf("#paper_sensor_out_input changed: %u -> %u\r\n", paper_sensor_out_input_last, paper_sensor_out_input);
            
			/* Broadcast the event */
			if (paper_sensor_out_input == 0) {
				//configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_OUT_PRESSED) & ebPAPER_SENSOR_OUT_PRESSED);
				uxReturned = xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_OUT_PRESSED);
				uxReturned = xEventGroupClearBits( xSBBEventGroup, ebPAPER_SENSOR_OUT_RELEASED );
			} else {
				uxReturned = xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_OUT_RELEASED);
				uxReturned = xEventGroupClearBits( xSBBEventGroup, ebPAPER_SENSOR_OUT_PRESSED );
				//configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_OUT_RELEASED) & ebPAPER_SENSOR_OUT_RELEASED);
			}
			printf("uxReturned = 0x%lx\r\n",uxReturned);
			paper_sensor_out_input_last = paper_sensor_out_input;
        }

		/* Cast button */
		cast_button_input = gpio_read(BUTTON_CAST_IN);
		if (cast_button_input != cast_button_input_last) {
            printf("#cast_button_input changed: %u -> %u\r\n", cast_button_input_last, cast_button_input);
            
			/* Broadcast the event */
			if (cast_button_input == 1) {
				//configASSERT(xEventGroupSetBits( xSBBEventGroup, ebCAST_BUTTON_PRESSED ) & ebCAST_BUTTON_PRESSED);
				uxReturned = xEventGroupSetBits( xSBBEventGroup, ebCAST_BUTTON_PRESSED );
				uxReturned = xEventGroupClearBits( xSBBEventGroup, ebCAST_BUTTON_RELEASED );
			} else {
				//configASSERT(xEventGroupSetBits( xSBBEventGroup, ebCAST_BUTTON_RELEASED ) & ebCAST_BUTTON_RELEASED);
				uxReturned = xEventGroupSetBits( xSBBEventGroup, ebCAST_BUTTON_RELEASED );
				uxReturned = xEventGroupClearBits( xSBBEventGroup, ebCAST_BUTTON_PRESSED );
			}
			printf("uxReturned = 0x%lx\r\n",uxReturned);
			cast_button_input_last = cast_button_input;
        }

		/* Spoil button */
		spoil_button_input = gpio_read(BUTTON_SPOIL_IN);
		if (spoil_button_input != spoil_button_input_last) {
            printf("#spoil_button_input changed: %u -> %u\r\n", spoil_button_input_last, spoil_button_input);
            
		/* Broadcast the event */
		if (spoil_button_input == 1) {
		    //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebSPOIL_BUTTON_PRESSED ) & ebSPOIL_BUTTON_PRESSED);
		    uxReturned = xEventGroupSetBits( xSBBEventGroup, ebSPOIL_BUTTON_PRESSED);
		    uxReturned = xEventGroupClearBits( xSBBEventGroup, ebSPOIL_BUTTON_RELEASED );
		} else {
		    //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebSPOIL_BUTTON_RELEASED ) & ebSPOIL_BUTTON_RELEASED);
		    uxReturned = xEventGroupSetBits( xSBBEventGroup, ebSPOIL_BUTTON_RELEASED );
		    uxReturned = xEventGroupClearBits( xSBBEventGroup, ebSPOIL_BUTTON_PRESSED );
		}
		printf("uxReturned = 0x%lx\r\n",uxReturned);
		spoil_button_input_last = spoil_button_input;
            }

        vTaskDelay(GPIO_READ_DELAY_MS);
	}
}

/*-----------------------------------------------------------*/
