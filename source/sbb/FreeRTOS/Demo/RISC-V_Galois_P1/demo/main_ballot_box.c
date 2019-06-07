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
#include <stdbool.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Drivers */
#include "bsp.h"
#include "ff.h" /* Declarations of FatFs API */
#include "diskio.h"


/* Smart Ballot Box includes */
#include "sbb.h"
#include "uart.h"

void main_ballot_box(void);

static void prvBallotBoxMainTask(void *pvParameters);
static void prvBarcodeScannerTask(void *pvParameters);
static void prvLoggingTask(void *pvParameters);
/*-----------------------------------------------------------*/

void main_ballot_box(void)
{
	xTaskCreate(prvBallotBoxMainTask, "prvBallotBoxMainTask", configMINIMAL_STACK_SIZE * 2U, NULL, tskIDLE_PRIORITY + 1, NULL);
	xTaskCreate(prvBarcodeScannerTask, "prvBarcodeScannerTask", configMINIMAL_STACK_SIZE * 2U, NULL, tskIDLE_PRIORITY + 1, NULL);
	xTaskCreate(prvLoggingTask, "prvLoggingTask", configMINIMAL_STACK_SIZE * 2U, NULL, tskIDLE_PRIORITY + 1, NULL);
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

	for (;;) {
		;;
	}
}

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
			set_received_barcode(barcode, idx);
            just_received_barcode();
            idx = 0;
			memset(barcode, 0, BARCODE_MAX_LENGTH);
        }
        else
        {
            idx++;
            if (idx >= BARCODE_MAX_LENGTH)
            {
                idx = 0;
            }
        }
        vTaskDelay(pdMS_TO_TICKS(10));
    }
}

