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
#include "gpio.h"

#include "uart.h"

/*-----------------------------------------------------------*/
#define MAIN_GPIO_DELAY_MS 100
/*-----------------------------------------------------------*/

/*
 * Called by main when PROG=main_gpio
 */
void main_gpio(void);

/*
 * The tasks as described in the comments at the top of this file.
 */
static void vTestGPIO_output(void *pvParameters);
static void vTestGPIO_input(void *pvParameters);
static void vTestLED(void *pvParameters);

/*-----------------------------------------------------------*/

void main_gpio(void)
{
    /* Create GPIO test */
    xTaskCreate(vTestGPIO_output, "GPIO Output Test", 1000, NULL, 0, NULL);
    xTaskCreate(vTestGPIO_input, "GPIO Input Test", 1000, NULL, 0, NULL);
    xTaskCreate(vTestLED, "LED Test", 1000, NULL, 0, NULL);
}
/*-----------------------------------------------------------*/

#define GPIO_INPUTS 4
#define GPIO_IN_4 4
#define GPIO_IN_5 5
#define GPIO_IN_6 6
#define GPIO_IN_7 7
void vTestGPIO_input(void *pvParameters)
{
    (void)pvParameters;

    printf("vTestGPIO_input starting\r\n");

    // GPIO Input has a pull-up, it is high unless pulled to the ground
    uint8_t input[GPIO_INPUTS] = {1};
    uint8_t input_last[GPIO_INPUTS] = {1};

    gpio_set_as_input(GPIO_IN_4);
    gpio_set_as_input(GPIO_IN_5);
    gpio_set_as_input(GPIO_IN_6);
    gpio_set_as_input(GPIO_IN_7);

    for (;;)
    {
        input[0] = gpio_read(GPIO_IN_4);
        input[1] = gpio_read(GPIO_IN_5);
        input[2] = gpio_read(GPIO_IN_6);
        input[3] = gpio_read(GPIO_IN_7);

        for (uint8_t idx = 0; idx < GPIO_INPUTS; idx++) {
            if (input[idx] != input_last[idx]) {
                printf("#%u changed: %u -> %u\r\n", idx, input_last[idx], input[idx]);
                input_last[idx] = input[idx];
            }
        }

        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
    }
}

#define GPIO_OUT_0 0
#define GPIO_OUT_1 1
#define GPIO_OUT_2 2
#define GPIO_OUT_3 3
void vTestGPIO_output(void *pvParameters)
{
    (void)pvParameters;

    printf("vTestGPIO_output starting\r\n");

    // Delay so the input thread can catch up
    vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

    gpio_set_as_output(GPIO_OUT_0);
    gpio_set_as_output(GPIO_OUT_1);
    gpio_set_as_output(GPIO_OUT_2);
    gpio_set_as_output(GPIO_OUT_3);

    /* GPIO are already set in hardware to be outputs */
    for (;;)
    {
        /***** WRITE TO PINS *****/
        gpio_write(GPIO_OUT_0);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        gpio_write(GPIO_OUT_1);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        gpio_write(GPIO_OUT_2);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        gpio_write(GPIO_OUT_3);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        gpio_write(GPIO_OUT_0);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        gpio_write(GPIO_OUT_1);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        gpio_write(GPIO_OUT_2);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        gpio_write(GPIO_OUT_3);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
    }
}

void vTestLED(void *pvParameters)
{
    (void)pvParameters;

    printf("vTestLED starting\r\n");

    for(;;)
    {
        /* Write to every LED */
        led_write(0);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_write(1);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_write(2);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_write(3);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_write(4);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_write(5);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_write(6);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_write(7);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));

        /* Clear every LED */
        led_clear(0);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_clear(1);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_clear(2);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_clear(3);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_clear(4);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_clear(5);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_clear(6);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
        led_clear(7);
        vTaskDelay(pdMS_TO_TICKS(MAIN_GPIO_DELAY_MS));
    }
}

/*-----------------------------------------------------------*/
