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
#include "event_groups.h"
#include "stream_buffer.h"

/* Standard includes */
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

/* Drivers */
#include "bsp.h"
#include "gpio.h"
#include "uart.h"

/* Smart Ballot Box includes */
#include "../logging/debug_io.h"
#include "sbb.h"
#include "sbb_freertos.h"

/* "Peek/poke" embedded web server */
#include "peekpoke.h"

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

/*-----------------------------------------------------------*/
/* Sample barcodes */
static char *valid_barcode_1 =
    "2019+07+31+22+22:1bk5cBJeyseBExT54lsVpS6Qk0hN_c3uuX4feV6D_-k=";
static char *valid_barcode_2 =
    "2019+07+31+22+22:vlj364nx6CD7wCTA0MCZkZNl4UCdrI_tHMJtcra8eAE=";
static char *valid_barcode_3 =
    "2019+07+31+22+20:vqj3MRalpCh5tCeiT7aq3frv9MXlY19-BOPIQEsGGtI=";

/*-----------------------------------------------------------*/

/*-----------------------------------------------------------*/
StreamBufferHandle_t xNetLogStreamBuffer;
StreamBufferHandle_t xScannerStreamBuffer;
EventGroupHandle_t xSBBEventGroup;
TaskHandle_t prvStartupTaskHandle = NULL;

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

    /* Initialize stream buffers */
    xScannerStreamBuffer =
        xStreamBufferCreate(sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1);
    xNetLogStreamBuffer =
        xStreamBufferCreate(sbLOG_BUFFER_SIZE, sbLOG_BUFFER_TRIGGER_LEVEL);
    /* Initialize event groups */
    xSBBEventGroup = xEventGroupCreate();
    configASSERT(xSBBEventGroup);

    // Initialize startup task
    xTaskCreate(prvStartupTask, "prvStartupTask", SBB_STARTUP_TASK_STACK_SIZE,
                NULL, SBB_STARTUP_TASK_PRIORITY, &prvStartupTaskHandle);

    // Setup TCP IP *after* all buffers and event groups are initialized
    sbb_tcp();

#if configGENERATE_RUN_TIME_STATS
    xTaskCreate(prvStatsTask, "prvStatsTask", configMINIMAL_STACK_SIZE * 10,
                NULL, SBB_STATS_TASK_PRIORITY, NULL);
#endif

    /* 
	 * Tells the peekPokeServer what its priority will be. The task won't
	 * launch until peekPokeServerTaskCreate() is called.
	 */
    peekPokeServerTaskPriority(SBB_PEEKPOKE_TASK_PRIORITY);

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

// Returns percentage utilization of the ISR stack
#include "portmacro.h"
extern const StackType_t xISRStackTop;
extern const uint32_t _stack_end[];
const StackType_t xISRStackEnd = (StackType_t)_stack_end;

static uint8_t prvIsrStackUtilization(void)
{
    uint8_t percent = 0;
    uint32_t idx;
    uint32_t stack_len = (xISRStackTop - xISRStackEnd) / 4; // # words
    uint32_t *stack_ptr = (uint32_t *)xISRStackEnd;

    //printf("xISRStackTop: 0x%lx\r\n",xISRStackTop);
    //printf("xISRStackEnd 0x%lx\r\n", xISRStackEnd);
    //printf("Stack len %lu\r\n",stack_len);

    for (idx = 0; idx < stack_len; idx++)
    {
        //printf("stack ptr addr %p\r\n", stack_ptr);
        //printf("stack ptr val 0x%lx\r\n", *stack_ptr);
        if (*stack_ptr != 0xabababab)
        {
            //printf("end of usable region\r\n");
            break;
        }
        stack_ptr++;
    }
    //printf("idx = %lu\r\n",idx);

    percent = 100 - idx * 100 / stack_len;

    return percent;
}

static void prvStatsTask(void *pvParameters)
{
    (void)pvParameters;
    printf(("prvStatsTask: starting\r\n"));
    vTaskDelay(pdMS_TO_TICKS(1000));

    for (;;)
    {
        vTaskGetRunTimeStats(statsBuffer);
        printf("prvStatsTask: xPortGetFreeHeapSize() = %u\r\n",
               xPortGetFreeHeapSize());
        printf("prvStatsTask: prvIsrStackUtilization() = %u\r\n",
               prvIsrStackUtilization());
        printf("prvStatsTask: Run-time "
               "stats\r\nTask\t\tAbsTime\t\t%%time\tStackHighWaterMark\r\n");
        printf("%s\r\n", statsBuffer);
        vTaskDelay(pdMS_TO_TICKS(10000));
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
void prvBallotBoxMainTask(void *pvParameters)
{
    (void)pvParameters;
    printf("Starting prvBallotBoxMainTask\r\n");

    ballot_box_main_loop();
}
/*-----------------------------------------------------------*/

/**
 * Aux task polling data from the barcode scanner
 */
void prvBarcodeScannerTask(void *pvParameters)
{
    (void)pvParameters;

    uint8_t idx = 0;
    char local_barcode[BARCODE_MAX_LENGTH] = {0};
    char buffer[17] = {0};
    buffer[16] = '\0';
    int len;

    printf("Starting prvBarcodeScannerTask\r\n");

    for (;;)
    {
        /* explicitly ask for at most 16 characters, as that is the FIFO limit */
        if (len > 0)
        {
            for (int i = 0; i < len; i++)
            {
                if (buffer[i] == 0xd)
                {
                    /* Send the barcode */
                    /* Debug print below */
                    local_barcode[idx] = '\0';
                    debug_printf("Barcode, idx=%u: %s\r\n", idx, local_barcode);
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
                                                   (void *)local_barcode,
                                                   (size_t)idx, 0) == idx);
                    /* Broadcast the event */
                    xEventGroupSetBits(xSBBEventGroup, ebBARCODE_SCANNED);
                    /* reset state */
                    idx = 0;
                    memset(local_barcode, 0, BARCODE_MAX_LENGTH);
                }
                else
                {
                    // copy over
                    local_barcode[idx] = buffer[i];
                    idx++;
                    idx %= sizeof(local_barcode);
                }
            }
        }

        /* Sleeping for 1 ms should be the right amount */
        msleep(1);
    }
}

/*-----------------------------------------------------------*/

static uint8_t prvNetworkLogTask_buf[sbLOG_BUFFER_SIZE] = {0};
/* ipconfigTCP_KEEP_ALIVE_INTERVAL defined in FreeRTOSIPConfig.h
 * is set to 20 seconds, hence sending a "ping" every 10 seconds
 * should be appropriate
 */
#define SBB_NETWORK_LOG_TASK_KEEP_ALIVE_DELAY pdMS_TO_TICKS(10000)
void prvNetworkLogTask(void *pvParameters)
{
    (void)pvParameters;

    Socket_t xSocket;
    BaseType_t res;
    struct freertos_sockaddr xRemoteAddress;
    BaseType_t xBytesSent = 0;
    size_t xLenToSend, xReceiveLength;

    printf("Starting prvNetworkLogTask\r\n");

#ifdef SIMULATION
    // NOTE: we could be using the hardcoded current time, but
    // this is better for variability in the seed
    uint32_t seed = uptimeMs();
#else
    uint32_t year_now;
    uint16_t month_now, day_now, hour_now, minute_now;
    configASSERT(get_current_time(&year_now, &month_now, &day_now, &hour_now,
                                  &minute_now));
    uint8_t month = (uint8_t)month_now;
    uint8_t day = (uint8_t)day_now;
    uint8_t hour = (uint8_t)hour_now;
    uint8_t minute = (uint8_t)minute_now;
    uint32_t seed = (uint32_t)(day | hour << 8 | minute << 16 | month << 24);
#endif /*S SIMULATION */
    debug_printf("Seed for randomiser: %lu\r\n", seed);
    prvSRand((uint32_t)seed);

    xRemoteAddress.sin_port = FreeRTOS_htons(LOG_PORT_NUMBER);
    xRemoteAddress.sin_addr =
        FreeRTOS_inet_addr_quick(configRptrIP_ADDR0, configRptrIP_ADDR1,
                                 configRptrIP_ADDR2, configRptrIP_ADDR3);

    xSocket = FreeRTOS_socket(FREERTOS_AF_INET, FREERTOS_SOCK_STREAM,
                              FREERTOS_IPPROTO_TCP);
    configASSERT(xSocket != FREERTOS_INVALID_SOCKET);

    res = FreeRTOS_connect(xSocket, &xRemoteAddress, sizeof(xRemoteAddress));
    if (res != 0)
    {
        printf("prvNetworkLogTask: cannot connect, res = %li\r\n", res);
        configASSERT(res == 0);
    }
    debug_printf("prvNetworkLogTask: socket connected\r\n");

    for (;;)
    {
#ifdef NETWORK_LOG_DEBUG
        debug_printf("prvNetworkLogTask: wainting for data\r\n");
#endif
        // Wait indefinitely for new data to send
        xReceiveLength =
            xStreamBufferReceive(xNetLogStreamBuffer, prvNetworkLogTask_buf,
                                 sizeof(prvNetworkLogTask_buf),
                                 SBB_NETWORK_LOG_TASK_KEEP_ALIVE_DELAY);
#ifdef NETWORK_LOG_DEBUG
        debug_printf("prvNetworkLogTask: Got %u bytes to send\r\n",
                     xReceiveLength);
#endif

        if (xReceiveLength == 0)
        {
/* @mpodhradsky: TODO: this should either be sending some HTTP request 
             * or the reporter needs to distinguish between valid data and "keep-alive"
             * content.
             */
#ifdef NETWORK_LOG_DEBUG
            debug_printf("prvNetworkLogTask: No new data available, sending "
                         "keep alive packet\r\n");
#endif
            xReceiveLength = 124;
            memset(prvNetworkLogTask_buf, '!', 124);
        }

        xLenToSend = 0;
        uint8_t iter = 0;
        do
        {
            iter++;
#ifdef NETWORK_LOG_DEBUG
            debug_printf("prvNetworkLogTask: #%u: xLenToSend: %u, "
                         "xReceiveLength: %u,\r\n",
                         iter, xLenToSend, xReceiveLength);
#endif
            xBytesSent =
                FreeRTOS_send(/* The socket being sent to. */
                              xSocket,
                              /* The data being sent. */
                              prvNetworkLogTask_buf + xLenToSend,
                              /* The remaining length of data to send. */
                              xReceiveLength - xLenToSend,
                              /* ulFlags. */
                              0);
#ifdef NETWORK_LOG_DEBUG
            debug_printf("prvNetworkLogTask: returned: %li\r\n", xBytesSent);
#endif
            if (xBytesSent < 0)
            {
                debug_printf("prvNetworkLogTask: ERROR writing "
                             "Transmit_Buffer to socket: %li\r\n",
                             xBytesSent);
                break;
            }

            if (xBytesSent == 0)
            {
                break;
            }
            xLenToSend += xBytesSent;
        } while (xLenToSend < xReceiveLength);
    }
    /* Initiate graceful shutdown. */
    debug_printf("prvNetworkLogTask: Closing the socket\r\n");
    FreeRTOS_shutdown(xSocket, FREERTOS_SHUT_RDWR);
    /* The socket has shut down and is safe to close. */
    FreeRTOS_closesocket(xSocket);
}

void prvStartupTask(void *pvParameters)
{
    (void)pvParameters;
    char buf[17] = {' '};
    uint8_t cnt = 0;
    clear_display();

    for (;;)
    {
        memset(buf, ' ', 16);
        buf[16] = 0;
        buf[cnt] = '.';
#ifndef SIMULATION
        display_this_text_no_log(buf, strlen(buf));
#endif
        printf("%s\r", buf);
        cnt++;
        cnt %= 16;
        msleep(1000);
    }
    printf("Terminating\r\n");
}

/* Task handling the GPIO inputs */
void prvInputTask(void *pvParameters)
{
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

    for (;;)
    {
        /* Paper sensor in */
        paper_sensor_in_input = gpio_read(PAPER_SENSOR_IN);
        if (paper_sensor_in_input != paper_sensor_in_input_last &&
            paper_in_timestamp + PAPER_SENSOR_DEBOUNCE < xTaskGetTickCount())
        {
            if (paper_sensor_in_input == 0)
            {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED) & ebPAPER_SENSOR_IN_PRESSED);
                debug_printf("#paper_sensor_in_input: paper_detected");
                uxReturned = xEventGroupSetBits(xSBBEventGroup,
                                                ebPAPER_SENSOR_IN_PRESSED);
                uxReturned = xEventGroupClearBits(xSBBEventGroup,
                                                  ebPAPER_SENSOR_IN_RELEASED);
            }
            else if (paper_sensor_in_input == 1)
            {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED) & ebPAPER_SENSOR_IN_RELEASED);
                debug_printf("#paper_sensor_in_input: no paper detected");
                uxReturned = xEventGroupSetBits(xSBBEventGroup,
                                                ebPAPER_SENSOR_IN_RELEASED);
                uxReturned = xEventGroupClearBits(xSBBEventGroup,
                                                  ebPAPER_SENSOR_IN_PRESSED);
            }
            paper_in_timestamp = xTaskGetTickCount();
            paper_sensor_in_input_last = paper_sensor_in_input;
            debug_printf("uxReturned = 0x%lx\r\n", uxReturned);
        }

        /* Cast button */
        cast_button_input = gpio_read(BUTTON_CAST_IN);
        if (cast_button_input != cast_button_input_last)
        {
            debug_printf("#cast_button_input changed: %u -> %u\r\n",
                         cast_button_input_last, cast_button_input);

            /* Broadcast the event */
            if (cast_button_input == 1)
            {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebCAST_BUTTON_PRESSED ) & ebCAST_BUTTON_PRESSED);
                uxReturned =
                    xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED);
                uxReturned = xEventGroupClearBits(xSBBEventGroup,
                                                  ebCAST_BUTTON_RELEASED);
            }
            else
            {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebCAST_BUTTON_RELEASED ) & ebCAST_BUTTON_RELEASED);
                uxReturned =
                    xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_RELEASED);
                uxReturned =
                    xEventGroupClearBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED);
            }
            debug_printf("uxReturned = 0x%lx\r\n", uxReturned);
            cast_button_input_last = cast_button_input;
        }

        /* Spoil button */
        spoil_button_input = gpio_read(BUTTON_SPOIL_IN);
        if (spoil_button_input != spoil_button_input_last)
        {
            debug_printf("#spoil_button_input changed: %u -> %u\r\n",
                         spoil_button_input_last, spoil_button_input);

            /* Broadcast the event */
            if (spoil_button_input == 1)
            {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebSPOIL_BUTTON_PRESSED ) & ebSPOIL_BUTTON_PRESSED);
                uxReturned =
                    xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_PRESSED);
                uxReturned = xEventGroupClearBits(xSBBEventGroup,
                                                  ebSPOIL_BUTTON_RELEASED);
            }
            else
            {
                //configASSERT(xEventGroupSetBits( xSBBEventGroup, ebSPOIL_BUTTON_RELEASED ) & ebSPOIL_BUTTON_RELEASED);
                uxReturned =
                    xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_RELEASED);
                uxReturned = xEventGroupClearBits(xSBBEventGroup,
                                                  ebSPOIL_BUTTON_PRESSED);
            }
            // printf("uxReturned = 0x%lx\r\n",uxReturned);
            spoil_button_input_last = spoil_button_input;
        }

        vTaskDelay(GPIO_READ_DELAY_MS);
    }
}

/*-----------------------------------------------------------*/

void sim_paper_sensor_in_pressed(void)
{
    printf("SIM: bPAPER_SENSOR_IN_PRESSED\r\n");
    xEventGroupSetBits(xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
    xEventGroupClearBits(xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
}

void sim_paper_sensor_in_released(void)
{
    printf("SIM: ebPAPER_SENSOR_IN_RELEASED\r\n");
    xEventGroupSetBits(xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED);
    xEventGroupClearBits(xSBBEventGroup, ebPAPER_SENSOR_IN_PRESSED);
}

void sim_valid_barcode_scanned(uint8_t id)
{
    switch (id)
    {
    case 1:
        printf("SIM: ebBARCODE1_SCANNED %s\r\n", valid_barcode_1);
        xEventGroupSetBits(xSBBEventGroup, ebBARCODE_SCANNED);
        xStreamBufferSend(xScannerStreamBuffer, (void *)valid_barcode_1,
                          strlen(valid_barcode_1),
                          SCANNER_BUFFER_TX_BLOCK_TIME_MS);
        break;
    case 2:
        printf("SIM: ebBARCODE2_SCANNED %s\r\n", valid_barcode_2);
        xEventGroupSetBits(xSBBEventGroup, ebBARCODE_SCANNED);
        xStreamBufferSend(xScannerStreamBuffer, (void *)valid_barcode_2,
                          strlen(valid_barcode_2),
                          SCANNER_BUFFER_TX_BLOCK_TIME_MS);
        break;
    case 3:
        printf("SIM: ebBARCODE3_SCANNED %s\r\n", valid_barcode_3);
        xEventGroupSetBits(xSBBEventGroup, ebBARCODE_SCANNED);
        xStreamBufferSend(xScannerStreamBuffer, (void *)valid_barcode_3,
                          strlen(valid_barcode_3),
                          SCANNER_BUFFER_TX_BLOCK_TIME_MS);
        break;
    default:
        printf("sim_valid_barcode_scanned: Unkown barcode id: %u\r\n", id);
        break;
    }
}

void sim_cast_button_pressed(void)
{
    printf("SIM: ebCAST_BUTTON_PRESSED\r\n");
    xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED);
    xEventGroupClearBits(xSBBEventGroup, ebCAST_BUTTON_RELEASED);
    vTaskDelay(pdMS_TO_TICKS(100));
    printf("SIM: ebCAST_BUTTON_RELEASED\r\n");
    xEventGroupSetBits(xSBBEventGroup, ebCAST_BUTTON_RELEASED);
    xEventGroupClearBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED);
}

void sim_spoil_button_pressed(void)
{
    printf("SIM: ebSPOIL_BUTTON_PRESSED\r\n");
    xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_PRESSED);
    xEventGroupClearBits(xSBBEventGroup, ebSPOIL_BUTTON_RELEASED);
    msleep(100);
    printf("SIM: ebSPOIL_BUTTON_RELEASED\r\n");
    xEventGroupSetBits(xSBBEventGroup, ebSPOIL_BUTTON_RELEASED);
    xEventGroupClearBits(xSBBEventGroup, ebSPOIL_BUTTON_PRESSED);
}
/*-----------------------------------------------------------*/
