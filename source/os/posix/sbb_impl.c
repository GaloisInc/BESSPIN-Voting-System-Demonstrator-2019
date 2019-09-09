#include "votingdefs.h"
#include "sbb.h"
#include <stdlib.h>
#include <pthread.h>
#include <errno.h>

osd_event_group_handle_t   xSBBEventGroup = NULL;
pthread_mutex_t            event_lock     = PTHREAD_MUTEX_INITIALIZER;
uint32_t                   event_flags    = 0;

osd_stream_buffer_handle_t xScannerStreamBuffer;

void set_event_flags(uint32_t flags_to_set);

#define timespec_to_ms(_tv) \
    ((_tv).tv_sec*1000) + ((_tv).tv_nsec/1000000)

void osd_msleep(uint64_t msec)
{
    struct timespec pause = { msec/1000, (msec%1000)*1000000 };
    nanosleep(&pause, NULL);
}
osd_timer_ticks_t
osd_get_ticks(void)
{
    struct timespec time;
    osd_assert(!clock_gettime(CLOCK_MONOTONIC, &time));
    osd_timer_ticks_t ms = timespec_to_ms(time);
    return ms;
}

uint8_t
osd_read_time(struct voting_system_time_t *time)
{
    (void)time;
    //TBD
    osd_assert(0);
    return 0;
}

osd_event_mask_t
osd_event_group_set_bits(osd_event_group_handle_t event_group,
                         osd_event_mask_t         bits_to_set)
{
    (void)event_group;
    (void)bits_to_set;
    osd_assert(0);
    return 0;
}


void
osd_format_time_str(struct voting_system_time_t *time, char *buf)
{
    sprintf(buf, "%4u+%2u+%2u+%2u+%2u",
            time->year, time->month, time->day, time->hour, time->minute);
}

osd_event_mask_t
osd_wait_for_event(osd_event_group_handle_t event_group,
                   osd_event_mask_t         bits_to_wait_for,
                   osd_event_clear_t        clear_on_exit,
                   osd_event_wait_type_t    wait_for_all_bits,
                   osd_timer_ticks_t        timeout) // in msec
{
    pthread_mutex_lock(&event_lock);
    uint32_t wait_res;
    uint32_t result = 0;
    uint32_t return_flags = 0;
    struct timespec timeout_spec; //= { timeout/1000, (timeout % 1000) * 1000000 };

    clock_gettime(CLOCK_REALTIME, &timeout_spec);
    timeout_spec.tv_sec  += timeout/1000;
    timeout_spec.tv_nsec += (timeout % 1000) * 1000000;
    if ( timeout_spec.tv_nsec > 999999999 ) {
        timeout_spec.tv_sec += 1;
        timeout_spec.tv_nsec -= 999999999;
    }

    do {
        wait_res = pthread_cond_timedwait(event_group,
                                          &event_lock,
                                          &timeout_spec);
        return_flags = event_flags;
        result = bits_to_wait_for & event_flags;
    } while ( (wait_for_all_bits == WAIT_ALL) &&
              (result != bits_to_wait_for) &&
              (wait_res != ETIMEDOUT) );

    if ( clear_on_exit == CLEAR_ON_EXIT ) {
        event_flags = event_flags & ~result;
    }

    pthread_mutex_unlock(&event_lock);
    return return_flags;
}

uint32_t osd_stream_buffer_receive(osd_stream_buffer_handle_t handle,
                                   void *pRxData,
                                   size_t xBufferLengthBytes,
                                   osd_timer_ticks_t max_block_time_ms)
{
    pthread_mutex_lock(handle->lock);
    size_t size = xBufferLengthBytes < handle->size ? xBufferLengthBytes
                                                    : handle->size;
    memcpy(pRxData, handle->pBuf, size);
    pthread_mutex_unlock(handle->lock);
    (void)max_block_time_ms;

    return size;
}

void set_event_flags(uint32_t flags_to_set)
{
    pthread_mutex_lock(&event_lock);
    event_flags |= flags_to_set;
    pthread_mutex_unlock(&event_lock);
    pthread_cond_signal(xSBBEventGroup);
}

void osd_sim_cast_button_pressed() {
    set_event_flags(ebCAST_BUTTON_PRESSED);
}

void osd_sim_spoil_button_pressed() {
    set_event_flags(ebSPOIL_BUTTON_PRESSED);
}

void osd_sim_cast_button_released() {
    set_event_flags(ebCAST_BUTTON_RELEASED);
}

void osd_sim_spoil_button_released() {
    set_event_flags(ebSPOIL_BUTTON_RELEASED);
}

void osd_sim_paper_sensor_in_pressed() {
    set_event_flags(ebPAPER_SENSOR_IN_PRESSED);
}

void osd_sim_paper_sensor_in_released() {
    set_event_flags(ebPAPER_SENSOR_IN_RELEASED);
}

void osd_sim_barcode_input() {
    pthread_mutex_lock(xScannerStreamBuffer->lock);
    if (xScannerStreamBuffer->pBuf) {
        free(xScannerStreamBuffer->pBuf);
    }
    xScannerStreamBuffer->pBuf = malloc(256);
    printf("Enter a barcode: ");
    scanf("%255s", xScannerStreamBuffer->pBuf);
    printf("\n");
    xScannerStreamBuffer->size = strlen(xScannerStreamBuffer->pBuf);
    printf("Read: [%s] Size: [%lu]\n", xScannerStreamBuffer->pBuf, xScannerStreamBuffer->size);
    pthread_mutex_unlock(xScannerStreamBuffer->lock);
    set_event_flags(ebBARCODE_SCANNED);
}

void osd_sim_initialize() {
    // Set up event group condition variable
    xSBBEventGroup = malloc(sizeof(*xSBBEventGroup));
    osd_assert(xSBBEventGroup != NULL);
    osd_assert(0 == pthread_cond_init(xSBBEventGroup, NULL));

    // Set up barcode scanner stream buffer
    xScannerStreamBuffer = malloc(sizeof(*xScannerStreamBuffer));
    osd_assert(xScannerStreamBuffer != NULL);

    xScannerStreamBuffer->pBuf = NULL;
    xScannerStreamBuffer->size = 0;
    osd_assert(0 == pthread_mutex_init(xScannerStreamBuffer->lock, NULL));
}
