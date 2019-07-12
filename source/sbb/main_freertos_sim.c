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

/* IP stack includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Application includes */
#include "SimpleUDPClientAndServer.h"
#include "SimpleTCPEchoServer.h"
#include "TCPEchoClient_SingleTasks.h"

/* FreeRTOS includes */
#include "event_groups.h"
#include "stream_buffer.h"

/* Standard includes */
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

/* Drivers */
#include "bsp.h"
#include "uart.h"

/* Smart Ballot Box includes */
#include "../logging/debug_io.h"
#include "sbb.h"
#include "sbb_freertos.h"

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
   within this file.  See https://www.freertos.org/a00016.html */
void vApplicationMallocFailedHook(void);
void vApplicationIdleHook(void);
void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName);
void vApplicationTickHook(void);

/* Smart Ballot Box Tasks and priorities*/
#define SBB_MAIN_TASK_PRIORITY tskIDLE_PRIORITY + 2
#define SBB_INPUT_TASK_PRIORITY tskIDLE_PRIORITY + 1

static void prvBallotBoxMainTask(void *pvParameters);
static void prvInputTask(void *pvParameters);

/*-----------------------------------------------------------*/
/* Scenario variables */

static char *valid_barcode = "SAMPLE_BARCODE_1_2_3";

static void manual_input(void);
static void run_scenario_1(void);
static void run_scenario_2(void);
static void run_scenario_3(void);
/*-----------------------------------------------------------*/

StreamBufferHandle_t xScannerStreamBuffer;
EventGroupHandle_t xSBBEventGroup;

/*-----------------------------------------------------------*/
extern void main_tcp(void);
extern void reportIPStatus(void);

/**
 * Main application entry
 */
int main(void)
{
    prvSetupHardware();
    printf("TCP Setup\r\n");
    main_tcp();

    /* Initialize stream buffers */
    xScannerStreamBuffer =
        xStreamBufferCreate(sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1);
    /* Initialize event groups */
    xSBBEventGroup = xEventGroupCreate();
    configASSERT(xSBBEventGroup);

    xTaskCreate(prvBallotBoxMainTask, "prvBallotBoxMainTask",
                configMINIMAL_STACK_SIZE * 2U, NULL, SBB_MAIN_TASK_PRIORITY,
                NULL);
    xTaskCreate(prvInputTask, "prvInputTask", configMINIMAL_STACK_SIZE * 2U,
                NULL, SBB_INPUT_TASK_PRIORITY, NULL);

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
}
/*-----------------------------------------------------------*/

/**
 * Runs the main ballot box code
 */
static void prvBallotBoxMainTask(void *pvParameters)
{
    (void)pvParameters;
    printf("Starting prvBallotBoxMainTask\r\n");
    debug_printf("DEBUG DEBUG DEBUG DEBUG!\r\n");

    ballot_box_main_loop();
}
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

/*-----------------------------------------------------------*/

/* Handle user inputs */
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
