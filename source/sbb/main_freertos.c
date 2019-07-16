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

/* FreeRTOS TCP Stack includes */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

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
#include "../logging/debug_io.h"

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
#define SBB_MAIN_TASK_PRIORITY tskIDLE_PRIORITY+1
#define SBB_SCANNER_TASK_PRIORITY tskIDLE_PRIORITY+2
#define SBB_INPUT_TASK_PRIORITY tskIDLE_PRIORITY+3

static void prvBallotBoxMainTask(void *pvParameters);
static void prvBarcodeScannerTask(void *pvParameters);
static void prvInputTask(void *pvParameters);

void sbb_tcp(void);
void reportIPStatus(void);

#ifdef SIMULATION
/*-----------------------------------------------------------*/
/* Scenario variables */

static char *valid_barcode = "SAMPLE_BARCODE_1_2_3";

static void manual_input(void);
static void run_scenario_1(void);
static void run_scenario_2(void);
static void run_scenario_3(void);
#endif
/*-----------------------------------------------------------*/

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

    // Setup TCP IP
    sbb_tcp();

    /* Initialize stream buffers */
    xScannerStreamBuffer = xStreamBufferCreate( sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1 );
    /* Initialize event groups */
    xSBBEventGroup = xEventGroupCreate();
    configASSERT( xSBBEventGroup );


    xTaskCreate(prvBallotBoxMainTask, "prvBallotBoxMainTask", configMINIMAL_STACK_SIZE * 2U, NULL, SBB_MAIN_TASK_PRIORITY, NULL);
    xTaskCreate(prvBarcodeScannerTask, "prvBarcodeScannerTask", configMINIMAL_STACK_SIZE * 2U, NULL, SBB_SCANNER_TASK_PRIORITY, NULL);
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
 * Aux task polling data from the barcode scanner
 */
static void prvBarcodeScannerTask(void *pvParameters)
{
    (void)pvParameters;

    uint8_t idx = 0;
    char barcode[BARCODE_MAX_LENGTH] = {0};
    char buffer[17] = {0};
    buffer[16] = '\0';
    int len;

    printf("Starting prvBarcodeScannerTask\r\n");

    for (;;)
    {
        /* explicitly ask for at most 16 characters, as that is the FIFO limit */
        len = uart1_rxbuffer(buffer, 16);

        if (len > 0)
        {
            for (int i = 0; i < len; i++)
            {
                if (buffer[i] == 0xd)
                {
                    /* Send the barcode */
                    /* Debug print below */
                    barcode[idx] = '\0';
                    debug_printf("Barcode, idx=%u: %s\r\n", idx, barcode);
                    /* We have a barcode, send it over stream buffer and fire the event */
                    size_t bytes_available =
                        xStreamBufferSpacesAvailable(xScannerStreamBuffer);
                    if (bytes_available < idx)
                    {
                        /* reset buffer */
                        configASSERT(xStreamBufferReset(xScannerStreamBuffer) ==
                                     pdPASS);
                    }
                    configASSERT(xStreamBufferSend(xScannerStreamBuffer,
                                                   (void *)barcode, (size_t)idx,
                                                   0) == idx);
                    /* Broadcast the event */
                    xEventGroupSetBits(xSBBEventGroup, ebBARCODE_SCANNED);
                    /* reset state */
                    idx = 0;
                    memset(barcode, 0, BARCODE_MAX_LENGTH);
                }
                else
                {
                    // copy over
                    barcode[idx] = buffer[i];
                    idx++;
                    idx %= sizeof(barcode);
                }
            }
        }

        /* Sleeping for 1 ms should be the right amount */
        msleep(1);
    }
}


/*-----------------------------------------------------------*/

/* Task handling the GPIO inputs */
#ifndef SIMULATION
static void prvInputTask(void *pvParameters) {
    (void)pvParameters;
    EventBits_t uxReturned;
    TickType_t paper_in_timestamp = 0;
    
    printf("Starting prvInputTask\r\n");

    /* Buttons are active high */
    uint8_t cast_button_input = 0;
    uint8_t cast_button_input_last = 0;
    uint8_t spoil_button_input = 0;
    uint8_t spoil_button_input_last = 0;

    /* Sensors are active low */
    uint8_t paper_sensor_in_input = 1;
    uint8_t paper_sensor_in_input_last = 1;

    gpio_set_as_input(BUTTON_CAST_IN);
    gpio_set_as_input(BUTTON_SPOIL_IN);
    gpio_set_as_input(PAPER_SENSOR_IN);

    for(;;) {
        /* Paper sensor in */
        paper_sensor_in_input = gpio_read(PAPER_SENSOR_IN);
        if (paper_sensor_in_input != paper_sensor_in_input_last &&
            paper_in_timestamp + PAPER_SENSOR_DEBOUNCE < xTaskGetTickCount()) {
            if (paper_sensor_in_input == 0) {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED) & ebPAPER_SENSOR_IN_PRESSED);
                debug_printf("#paper_sensor_in_input: paper_detected");
                uxReturned = xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
                uxReturned = xEventGroupClearBits( xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
            } else if (paper_sensor_in_input == 1) {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED) & ebPAPER_SENSOR_IN_RELEASED);
                debug_printf("#paper_sensor_in_input: no paper detected");
                uxReturned = xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
                uxReturned = xEventGroupClearBits( xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
            }
            paper_in_timestamp = xTaskGetTickCount();
            paper_sensor_in_input_last = paper_sensor_in_input;
            // printf("uxReturned = 0x%lx\r\n",uxReturned);
        }

        /* Cast button */
        cast_button_input = gpio_read(BUTTON_CAST_IN);
        if (cast_button_input != cast_button_input_last) {
            debug_printf("#cast_button_input changed: %u -> %u\r\n", cast_button_input_last, cast_button_input);

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
            // printf("uxReturned = 0x%lx\r\n",uxReturned);
            cast_button_input_last = cast_button_input;
        }

        /* Spoil button */
        spoil_button_input = gpio_read(BUTTON_SPOIL_IN);
        if (spoil_button_input != spoil_button_input_last) {
            debug_printf("#spoil_button_input changed: %u -> %u\r\n", spoil_button_input_last, spoil_button_input);

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
            // printf("uxReturned = 0x%lx\r\n",uxReturned);
            spoil_button_input_last = spoil_button_input;
        }

        vTaskDelay(GPIO_READ_DELAY_MS);
    }
}
#else
/* Manually handle user inputs */
static void prvInputTask(void *pvParameters)
{
    (void)pvParameters;

    char *intro = "Choose a scenario:\r\n\
    1 - cast valid ballot\r\n\
    2 - spoil valid ballot\r\n\
    3 - try casting an invalid ballot(no barcode)\r\n\
    0 - manual mode\r\n\
    \r\n";

    printf("Starting prvInputTask\r\n");
    printf("%s", intro);


    for (;;)
    {
        char c = uart0_rxchar();
        if (c == 0xFF)
        {
            continue;
        }
        printf("%c\r\n", c);
        switch (c)
        {
        case '1':
            run_scenario_1();
            break;
        case '2':
            run_scenario_2();
            break;
        case '3':
            run_scenario_3();
            break;
        case '0':
            manual_input();
            break;
        case 't':
	    reportIPStatus();
            break;
        default:
            printf("Unknown command\r\n");
            printf("%s", intro);
            break;
        }
    }
}

/*-----------------------------------------------------------*/

#define SIM_PAPER_SENSOR_IN_PRESSED() printf("SIM: bPAPER_SENSOR_IN_PRESSED\r\n"); \
    xEventGroupSetBits(xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED); \
    xEventGroupClearBits(xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);

#define SIM_VALID_BARCODE_SCANNED() printf("SIM: ebBARCODE_SCANNED\r\n"); \
    xEventGroupSetBits(xSBBEventGroup, ebBARCODE_SCANNED); \
    xStreamBufferSend(xScannerStreamBuffer, (void *)valid_barcode, \
                      sizeof(valid_barcode), SCANNER_BUFFER_TX_BLOCK_TIME_MS);

#define SIM_PAPER_SENSOR_IN_RELEASED() printf("SIM: ebPAPER_SENSOR_IN_RELEASED\r\n"); \
    xEventGroupSetBits(xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED); \
    xEventGroupClearBits(xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);

#define SIM_CAST_BUTTON_PRESSED() printf("SIM: ebCAST_BUTTON_PRESSED\r\n"); \
    xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED); \
    xEventGroupClearBits(xSBBEventGroup, ebCAST_BUTTON_RELEASED); \
    vTaskDelay(pdMS_TO_TICKS(100)); \
    printf("SIM: ebCAST_BUTTON_RELEASED\r\n"); \
    xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_RELEASED); \
    xEventGroupClearBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED)

#define SIM_SPOIL_BUTTON_PRESSED() printf("SIM: ebSPOIL_BUTTON_PRESSED\r\n"); \
    xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_PRESSED); \
    xEventGroupClearBits(xSBBEventGroup, ebSPOIL_BUTTON_RELEASED); \
    msleep(100); \
    printf("SIM: ebSPOIL_BUTTON_RELEASED\r\n"); \
    xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_RELEASED); \
    xEventGroupClearBits(xSBBEventGroup, ebSPOIL_BUTTON_PRESSED);

/*-----------------------------------------------------------*/

/**
 * Scenario 1 - cast valid ballot
 */
static void run_scenario_1(void)
{
    printf("Scenario 1 - cast valid ballot\r\n");

    SIM_PAPER_SENSOR_IN_PRESSED();

    msleep(3000);

    SIM_VALID_BARCODE_SCANNED();

    msleep(5000);

    SIM_CAST_BUTTON_PRESSED();

    msleep(1000);

    SIM_PAPER_SENSOR_IN_RELEASED();

    msleep(1000);

    printf("Scenario 1 - done\r\n");
}

/*-----------------------------------------------------------*/

/**
 * Scenario 2 - spoil valid ballot
 */
static void run_scenario_2(void)
{
    printf("Scenario 2 - spoil valid ballot\r\n");

    SIM_PAPER_SENSOR_IN_PRESSED();

    msleep(3000);

    SIM_VALID_BARCODE_SCANNED();

    msleep(5000);

    SIM_SPOIL_BUTTON_PRESSED();

    msleep(3000);

    SIM_PAPER_SENSOR_IN_RELEASED();

    msleep(1000);

    printf("Scenario 2 - done\r\n");
}

/*-----------------------------------------------------------*/


/**
 * Scenario 3 - try casting invalid ballot
 */
static void run_scenario_3(void)
{
    printf("Scenario 3 - try casting invalid ballot\r\n");

    SIM_PAPER_SENSOR_IN_PRESSED();

    msleep(5000);

    SIM_CAST_BUTTON_PRESSED();

    msleep(5000);

    SIM_PAPER_SENSOR_IN_RELEASED();

    msleep(1000);

    printf("Scenario 3 - done\r\n");
}

#endif

/*-----------------------------------------------------------*/

/**
 * Manaul event input
 */
static void manual_input(void)
{
    char *help = "You can toggle the following events:\r\n \
     a - press Cast button (ebCAST_BUTTON_PRESSED)\r\n \
     b - release Cast button (ebCAST_BUTTON_RELEASED)\r\n \
     c - press Spoil button (ebSPOIL_BUTTON_PRESSED)\r\n \
     d - release Spoil button (ebSPOIL_BUTTON_PRESSED)\r\n \
     e - activate Paper In sensor (ebPAPER_SENSOR_IN_PRESSED)\r\n \
     f - deactivate Paper In sensor (ebPAPER_SENSOR_IN_RELEASE)\r\n \
     g - scan and send Barcode(ebBARCODE_SCANNED)\r\n \
     x - return to main menu\r\n\
     \r\n";

    printf("%s", help);

    for (;;)
    {
        char c = uart0_rxchar();
        if (c == 0xFF)
        {
            continue;
        }
        printf("%c\r\n", c);
        switch (c)
        {
        case 'a':
            printf("SIM: ebCAST_BUTTON_PRESSED\r\n");
            xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED);
            xEventGroupClearBits(xSBBEventGroup, ebCAST_BUTTON_RELEASED);
            break;
        case 'b':
            printf("SIM: ebCAST_BUTTON_RELEASED\r\n");
            xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_RELEASED);
            xEventGroupClearBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED);
            break;
        case 'c':
            printf("SIM: ebSPOIL_BUTTON_PRESSED\r\n");
            xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_PRESSED);
            xEventGroupClearBits(xSBBEventGroup, ebSPOIL_BUTTON_RELEASED);
            break;
        case 'd':
            printf("SIM: ebSPOIL_BUTTON_RELEASED\r\n");
            xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_RELEASED);
            xEventGroupClearBits(xSBBEventGroup, ebSPOIL_BUTTON_PRESSED);
            break;
        case 'e':
            printf("SIM: ebPAPER_SENSOR_IN_PRESSED\r\n");
            xEventGroupSetBits(xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
            xEventGroupClearBits(xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
            break;
        case 'f':
            printf("SIM: ebPAPER_SENSOR_IN_RELEASED\r\n");
            xEventGroupSetBits(xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
            xEventGroupClearBits(xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
            break;
        case 'g':
            printf("SIM: ebBARCODE_SCANNED\r\n");
            xEventGroupSetBits(xSBBEventGroup, ebBARCODE_SCANNED);
            xStreamBufferSend(xScannerStreamBuffer, (void *)valid_barcode,
                              sizeof(valid_barcode),
                              SCANNER_BUFFER_TX_BLOCK_TIME_MS);
            xEventGroupClearBits(xSBBEventGroup, ebBARCODE_SCANNED);
            break;
        case 'x':
            printf("Returning to main menu\r\n");
            return;
        case 'h':
            printf("%s", help);
            break;
        default:
            printf("Unknown command\r\n");
            printf("%s", help);
            break;
        }
    }
}
