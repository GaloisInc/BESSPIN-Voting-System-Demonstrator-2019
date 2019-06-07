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

/*
 * main_gpio() creates one task to test the GPIO and then starts the
 * scheduler.
 */

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo includes. */
#include "uart.h"

void main_uart(void);

/*
 * The tasks as described in the comments at the top of this file.
 */
static void vTestUART1Tx(void *pvParameters);
static void vTestUART1Rx(void *pvParameters);

/*-----------------------------------------------------------*/

void main_uart(void)
{
    /* Create GPIO test */
    xTaskCreate(vTestUART1Tx, "UART1 Tx Test", 1000, NULL, 0, NULL);
    xTaskCreate(vTestUART1Rx, "UART1 Rx Test", 1000, NULL, 0, NULL);
}
/*-----------------------------------------------------------*/

static void vTestUART1Tx(void *pvParameters)
{
	(void)pvParameters;

    char* msg = "Hello from UART1\n";
	printf("Starting vTestUART1 Tx\r\n");

	for (;;)
	{
		configASSERT(uart1_txbuffer(msg, strlen(msg)) != -1);
		vTaskDelay(pdMS_TO_TICKS(1000));
	}
}

static void vTestUART1Rx(void *pvParameters)
{
	(void)pvParameters;
	char str[20];
    uint8_t idx = 0;

	printf("Starting vTestUART1 Rx\r\n");
	for (;;)
	{
        configASSERT( uart1_rxbuffer(&str[idx], 1) != -1);
        if (str[idx] == '\n') { // End character received
             str[idx] = '\0'; // proper termination
             printf("UART1 RX: %s\r\n", str);
             idx=0;
        } else {
            idx++;
            idx %= sizeof(str);
        }
	}
}

/*-----------------------------------------------------------*/
