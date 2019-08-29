#ifndef __VOTINGDEFS_POSIX__
#define __VOTINGDEFS_POSIX__
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <FreeRTOS.h>
#include <task.h>
#include "event_groups.h"
#include "stream_buffer.h"
#include "semphr.h"
#include "bsp.h"
#include "gpio.h"
#include "serLcd.h"
#include "ds1338rtc.h"
#include "crypto/crypto.h"

/* Macros */
#define osd_assert configASSERT

/* Crypto */
const uint8_t *osd_fetch_key(AES_Key_Name key);

/* Time */
typedef TickType_t osd_timer_ticks_t;
#define osd_get_ticks     xTaskGetTickCount
#define osd_msec_to_ticks pdMS_TO_TICKS
#define osd_msleep        msleep

uint8_t
osd_read_time(struct voting_system_time_t *time);

void
osd_format_time_str(struct voting_system_time_t *time, char *buf);

/* Events */
typedef EventGroupHandle_t osd_event_group_handle_t;
typedef EventBits_t        osd_event_mask_t;

typedef enum { CLEAR_ON_EXIT=pdTRUE, DO_NOT_CLEAR_ON_EXIT=pdFALSE } osd_event_clear_t;
typedef enum { WAIT_ALL=pdTRUE, WAIT_ANY=pdFALSE } osd_event_wait_type_t;

#define osd_event_group_set_bits xEventGroupSetBits
#define osd_wait_for_event xEventGroupWaitBits

/* Streaming */
typedef StreamBufferHandle_t osd_stream_buffer_handle_t;

/*@ requires \valid((char *)pvRxData + (0 .. xBufferLengthBytes-1));
  @ assigns *((char *)pvRxData + (0 .. \result - 1));
  @ ensures 0 <= \result;
  @ ensures \result <= xBufferLengthBytes;
*/
extern size_t
xStreamBufferReceive(StreamBufferHandle_t h,
                     void *pvRxData,
                     size_t xBufferLengthBytes,
                     TickType_t timeout);
#define osd_stream_buffer_receive xStreamBufferReceive

#endif
