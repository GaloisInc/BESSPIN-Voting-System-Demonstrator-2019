#ifndef __VOTINGDEFS_POSIX__
#define __VOTINGDEFS_POSIX__
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <unistd.h>
#include <time.h>
#include <assert.h>
#include "crypto/crypto.h"
#include "log_os_defs.h"

/* Macros */
#define osd_assert(x) assert(x)

/* Crypto */
const uint8_t *osd_fetch_key (AES_Key_Name key);

/* Time */
typedef uint32_t osd_timer_ticks_t;
osd_timer_ticks_t osd_get_ticks(void);
#define osd_msec_to_ticks(x) (x)
#define osd_msleep(_x) usleep(1000*(_x))

uint8_t
osd_read_time(struct voting_system_time_t *time);
void
osd_format_time_str(struct voting_system_time_t *time, char *buf);

/* Events */
typedef uint32_t osd_event_group_handle_t;
typedef uint32_t osd_event_mask_t;

typedef enum { CLEAR_ON_EXIT, DO_NOT_CLEAR_ON_EXIT } osd_event_clear_t;
typedef enum { WAIT_ALL, WAIT_ANY } osd_event_wait_type_t;

osd_event_mask_t
osd_event_group_set_bits(osd_event_group_handle_t event_group,
                         osd_event_mask_t         bits_to_set);

osd_event_mask_t
osd_wait_for_event(osd_event_group_handle_t event_group,
                   osd_event_mask_t         bits_to_wait_for,
                   osd_event_clear_t        clear_on_exit,
                   osd_event_wait_type_t    wait_for_all_bits,
                   osd_timer_ticks_t        timeout);

/* Streaming */
typedef uint32_t osd_stream_buffer_handle_t;

/*@ requires \valid((char *)pvRxData + (0 .. xBufferLengthBytes-1));
  @ assigns *((char *)pvRxData + (0 .. \result - 1));
  @ ensures 0 <= \result;
  @ ensures \result <= xBufferLengthBytes;
*/
uint32_t osd_stream_buffer_receive(osd_stream_buffer_handle_t handle,
                                   void *pvRxData,
                                   size_t xBufferLengthBytes,
                                   osd_timer_ticks_t max_block_time_ms);

#endif
