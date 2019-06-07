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

// Drivers
#include "iic.h"

#if !(BSP_USE_IIC0)
#error "One or more peripherals are nor present, this test cannot be run"
#endif

// the i2c address
#define MPU925X_I2CADDR_DEFAULT 0x69 // AD0 = 1 (high)

#define WHOAMI_REGISTER_ADDR 117
#define WHOAMI_DEFAULT_RESPONSE 0x71

void main_iic(void);

static void prvIicTestTask0(void *pvParameters);
/*-----------------------------------------------------------*/

void main_iic(void)
{
	xTaskCreate(prvIicTestTask0, "prvIicTestTask0", configMINIMAL_STACK_SIZE * 2U, NULL, tskIDLE_PRIORITY + 1, NULL);
}
/*-----------------------------------------------------------*/


static void prvIicTestTask0(void *pvParameters)
{
	(void)pvParameters;

	printf("Starting prvIicTestTask0\r\n");
	uint8_t cnt = 0;
	uint8_t data = 0;

	// Give the sensor time to power up
	vTaskDelay(pdMS_TO_TICKS(100));

	for (;;)
	{
		data = WHOAMI_REGISTER_ADDR;
    	configASSERT(iic0_transmit(MPU925X_I2CADDR_DEFAULT, &data, 1) != -1);
		configASSERT(iic0_receive(MPU925X_I2CADDR_DEFAULT, &data, 1) != -1);
		configASSERT(data == WHOAMI_DEFAULT_RESPONSE);

		if (cnt > 2) {
			// Run twice before printing the output
			printf("Whoami: 0x%X\r\n",data);
		}

		cnt++;
		vTaskDelay(pdMS_TO_TICKS(1000));
	}
}
