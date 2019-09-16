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
#include "log_os_defs.h"

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

#define noop ((void)0)
#define noop1(x) ((void)x)
#define noop2(x, y) do { noop1(x); noop1(y); } while (0)
#define noop4(w, x, y, z) do { noop1(w); noop1(x); noop1(y); noop1(z); } while(0)
/* Display */
#ifndef SIMULATION
#define osd_clear_lcd()             serLcdClear()
#define osd_lcd_printf(_text, _len) serLcdPrintf((_text), (_len))
#define osd_lcd_printf_two_lines(_text1, _text2, _len1, _len2) \
    serLcdPrintTwoLines((_text1), (_text2), (_len1), (_len2))
#else
#define osd_clear_lcd()          noop
#define osd_lcd_printf           noop2
#define osd_lcd_printf_two_lines noop4
#endif

/* GPIO */
#ifndef SIMULATION
#define osd_gpio_set_as_input  gpio_set_as_input
#define osd_gpio_set_as_output gpio_set_as_output
#define osd_gpio_write         gpio_write
#define osd_gpio_clear         gpio_clear
#else
#define osd_gpio_set_as_input(x)  noop
#define osd_gpio_set_as_output(x) noop
#define osd_gpio_write(x)         noop
#define osd_gpio_clear(x)         noop
#endif

// Assigns declarations for FreeRTOS functions; these may not be
// accurate but are currently required to avoid crashing wp.

//@ assigns \nothing;
extern void serLcdPrintf(char *str, uint8_t len);
//@ assigns \nothing;
extern void serLcdPrintTwoLines(char *line_1, uint8_t len_1, char *line_2,
                                uint8_t len_2);


/*@ assigns the_firmware_state; */
extern void gpio_set_as_input(uint8_t);

/*@ requires 0 <= i && i < 8;
  @ assigns the_firmware_state;
  @ assigns gpio_mem[i];
  @ ensures gpio_mem[i] == 0;
  @*/
extern void gpio_set_as_output(uint8_t i);

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
