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
#include "stream_buffer.h"

/* Standard includes */
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

/* Drivers */
#include "bsp.h"
#include "diskio.h"
#include "ff.h" /* Declarations of FatFs API */

/* Logging subsystem includes */
#include "log.h"

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
#define SBB_LOGGING_TASK_PRIORITY tskIDLE_PRIORITY + 2

StreamBufferHandle_t xNetLogStreamBuffer;
#define sbLOG_BUFFER_SIZE 1024
#define sbLOG_BUFFER_TRIGGER_LEVEL 331

static void prvLoggingTask(void *pvParameters);
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
    asm volatile("%=:\n\t"
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

    xNetLogStreamBuffer =
        xStreamBufferCreate(sbLOG_BUFFER_SIZE, sbLOG_BUFFER_TRIGGER_LEVEL);

    xTaskCreate(prvLoggingTask, "prvLoggingTask", configMINIMAL_STACK_SIZE * 2U,
                NULL, SBB_LOGGING_TASK_PRIORITY, NULL);

#if configGENERATE_RUN_TIME_STATS
    xTaskCreate(prvStatsTask, "prvStatsTask", configMINIMAL_STACK_SIZE * 2,
                NULL, tskIDLE_PRIORITY, NULL);
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
        printf("prvStatsTask: xPortGetFreeHeapSize() = %u\r\n",
               xPortGetFreeHeapSize());
        printf(
            "prvStatsTask: Run-time stats\r\nTask\tAbsTime\tpercent_time\r\n");
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
 * Logs data onto the SD card
 */
static void prvLoggingTask(void *pvParameters)
{
    (void)pvParameters;

    printf("Starting prvLoggingTask\r\n");

    Log_Handle my_log;

    Log_IO_Initialize();

    create_log(&my_log, "test1log.txt", HTTP_Endpoint_None);

    Log_IO_Close(&my_log);
    printf("prvLoggingTask terminating\r\n");
}
/*-----------------------------------------------------------*/
