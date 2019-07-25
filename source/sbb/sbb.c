/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

// General includes
#include <stdio.h>
#include <string.h>

// FreeRTOS specific includes
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

// Subsystem includes
#include "sbb.h"
#include "sbb_crypto.h"
#include "sbb_freertos.h"
#include "sbb_logging.h"

// BESSPIN Voting System devices
#include "ds1338rtc.h"
#include "gpio.h"
#include "serLcd.h"

TickType_t ballot_detect_timeout = 0;
TickType_t cast_or_spoil_timeout = 0;

char barcode[BARCODE_MAX_LENGTH] = {0};
barcode_length_t barcode_length = 0;

// Assigns declarations for FreeRTOS functions; these may not be
// accurate but are currently required to avoid crashing wp.

//@ assigns \nothing;
extern void serLcdPrintf(char *str, uint8_t len);
//@ assigns \nothing;
extern void serLcdPrintTwoLines(char *line_1, uint8_t len_1, char *line_2,
                                uint8_t len_2);

//@ assigns \nothing;
extern EventBits_t xEventGroupWaitBits(EventGroupHandle_t xEventGroup,
                                       const EventBits_t uxBitsToWaitFor,
                                       const BaseType_t xClearOnExit,
                                       const BaseType_t xWaitForAllBits,
                                       TickType_t xTicksToWait);

// main code
/*@ assigns the_firmware_state; */
extern void gpio_set_as_input(uint8_t);

/*@ assigns the_firmware_state; */
extern void gpio_set_as_output(uint8_t);

void initialize(void)
{
    gpio_set_as_input(BUTTON_CAST_IN);
    gpio_set_as_input(BUTTON_SPOIL_IN);
    gpio_set_as_input(PAPER_SENSOR_IN);
    gpio_set_as_input(PAPER_SENSOR_OUT);
    gpio_set_as_output(MOTOR_0);
    gpio_set_as_output(MOTOR_1);
    gpio_set_as_output(BUTTON_CAST_LED);
    gpio_set_as_output(BUTTON_SPOIL_LED);
    the_state.button_illumination = 0;
    // Logging is not set up yet...we could do that here I suppose
    the_state.M = MOTORS_OFF;
    the_state.D = INITIALIZED_DISPLAY;
    the_state.BS = BARCODE_NOT_PRESENT;
    __assume_strings_OK();
    barcode_length = 0;
    return;
}

/* global invariant Button_lighting_conditions_power_on:
   \forall cast_button_light cbl, spoil_button_light sbl;
   \at(lights_off(cbl, sbl), DevicesInitialized);
*/

/* global invariant Paper_ejected_on_power_on:
   \forall paper_present p; \at(p == none, DevicesInitialized);
*/

/* global invariant Motor_initial_state:
   \forall motor m; \at(!motor_running(m), DevicesInitialized);
*/
bool is_barcode_valid(barcode_t the_barcode, barcode_length_t its_length)
{
    return crypto_check_barcode_valid(the_barcode, its_length);
}

bool is_cast_button_pressed(void) { return the_state.B == CAST_BUTTON_DOWN; }

bool is_spoil_button_pressed(void) { return the_state.B == SPOIL_BUTTON_DOWN; }

void set_received_barcode(barcode_t the_barcode, barcode_length_t its_length)
{
    configASSERT(its_length <= BARCODE_MAX_LENGTH);
    memcpy(barcode, the_barcode, its_length);
    barcode_length = its_length;
}

bool has_a_barcode(void)
{
    return the_state.BS == BARCODE_PRESENT_AND_RECORDED;
}

barcode_length_t what_is_the_barcode(barcode_t the_barcode)
{
    memcpy(the_barcode, barcode, barcode_length);
    __assume_strings_OK();
    return barcode_length;
}

void spoil_button_light_on(void)
{
#ifndef SIMULATION
    gpio_write(BUTTON_SPOIL_LED);
#endif
    the_state.button_illumination |= spoil_button_mask;
}

void spoil_button_light_off(void)
{
#ifndef SIMULATION
    gpio_clear(BUTTON_SPOIL_LED);
#endif
    the_state.button_illumination &= ~spoil_button_mask;
}

void cast_button_light_on(void)
{
#ifndef SIMULATION
    gpio_write(BUTTON_CAST_LED);
#endif
    the_state.button_illumination |= cast_button_mask;
}

void cast_button_light_off(void)
{
#ifndef SIMULATION
    gpio_clear(BUTTON_CAST_LED);
#endif
    the_state.button_illumination &= ~cast_button_mask;
}

void move_motor_forward(void)
{
#ifndef SIMULATION
    gpio_clear(MOTOR_0);
    gpio_write(MOTOR_1);
#endif
    CHANGE_STATE(the_state, M, MOTORS_TURNING_FORWARD);
}

void move_motor_back(void)
{
#ifndef SIMULATION
    gpio_write(MOTOR_0);
    gpio_clear(MOTOR_1);
#endif
    CHANGE_STATE(the_state, M, MOTORS_TURNING_BACKWARD);
}

void stop_motor(void)
{
#ifndef SIMULATION
    gpio_clear(MOTOR_0);
    gpio_clear(MOTOR_1);
#endif
    CHANGE_STATE(the_state, M, MOTORS_OFF);
}

void clear_display(void)
{
#ifndef SIMULATION
    serLcdClear();
#endif
}

void display_this_text_no_log(const char *the_text, uint8_t its_length)
{
#ifdef SIMULATION
    (void)its_length;
    debug_printf("DISPLAY: %s\r\n", the_text);
#else
    serLcdPrintf((char *)the_text, its_length);
#endif    
}

void display_this_text(const char *the_text, uint8_t its_length)
{
#ifdef SIMULATION
    (void)its_length;
    debug_printf("DISPLAY: %s\r\n", the_text);
#else
    serLcdPrintf((char *)the_text, its_length);
#endif
    CHANGE_STATE(the_state, D, SHOWING_TEXT);
}

void display_this_2_line_text(const char *line_1, uint8_t length_1,
                              const char *line_2, uint8_t length_2)
{
#ifdef SIMULATION
    (void)length_1;
    (void)length_2;
    debug_printf("DISPLAY: %s\r\nLINETWO: %s\r\n", line_1, line_2);
#else
    CHANGE_STATE(the_state, D, SHOWING_TEXT);
    serLcdPrintTwoLines((char *)line_1, length_1, (char *)line_2, length_2);
#endif
}

bool ballot_detected(void) { return (the_state.P == PAPER_DETECTED); }

void eject_ballot(void)
{
    move_motor_back();
    // run the motor for a bit to get the paper back over the switch
    msleep(SPOIL_EJECT_TIMEOUT_MS);
    stop_motor();
}

void spoil_ballot(void)
{
    spoil_button_light_off();
    cast_button_light_off();
    display_this_text(spoiling_ballot_text, strlen(spoiling_ballot_text));
    eject_ballot();
}

void cast_ballot(void)
{
    spoil_button_light_off();
    cast_button_light_off();
    move_motor_forward();
    msleep(CAST_INGEST_TIMEOUT_MS);
    stop_motor();
}

void go_to_standby(void)
{
    if (the_state.M != MOTORS_OFF)
    {
        stop_motor();
    }
    cast_button_light_off();
    spoil_button_light_off();
    display_this_2_line_text(welcome_text, strlen(welcome_text),
                             insert_ballot_text, strlen(insert_ballot_text));
    CHANGE_STATE(the_state, M, MOTORS_OFF);
    CHANGE_STATE(the_state, D, SHOWING_TEXT);
    CHANGE_STATE(the_state, P, NO_PAPER_DETECTED);
    CHANGE_STATE(the_state, BS, BARCODE_NOT_PRESENT);
    CHANGE_STATE(the_state, S, INNER);
    CHANGE_STATE(the_state, B, ALL_BUTTONS_UP);
    CHANGE_STATE(the_state, L, STANDBY);
}

//@ assigns ballot_detect_timeout;
void ballot_detect_timeout_reset(void)
{
    ballot_detect_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(BALLOT_DETECT_TIMEOUT_MS);
}

bool ballot_detect_timeout_expired(void)
{
    return (xTaskGetTickCount() > ballot_detect_timeout);
}

//@ assigns cast_or_spoil_timeout;
void cast_or_spoil_timeout_reset(void)
{
    cast_or_spoil_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(CAST_OR_SPOIL_TIMEOUT_MS);
}

bool cast_or_spoil_timeout_expired(void)
{
    return (xTaskGetTickCount() > cast_or_spoil_timeout);
}

TickType_t ballot_detect_timeout_remaining(void) {
    return (ballot_detect_timeout - xTaskGetTickCount());
}

TickType_t cast_or_spoil_timeout_remaining(void) {
    return (cast_or_spoil_timeout - xTaskGetTickCount());
}


/**
 * Attempt to read current RTC time 
 */
bool get_current_time(uint32_t *year, uint16_t *month, uint16_t *day,
                      uint16_t *hour, uint16_t *minute)
{
    static struct rtctime_t time;
    if (ds1338_read_time(&time) == 0)
    {
        *year = (uint32_t)time.year;
        *month = (uint16_t)time.month;
        *day = (uint16_t)time.day;
        *hour = (uint16_t)time.hour;
        *minute = (uint16_t)time.minute;

#ifdef VOTING_SYSTEM_DEBUG
        // A character array to hold the string representation of the time
        static char time_str[20];
        format_time_str(&time, time_str);
        printf("Get current time:  %s\r\n",time_str);
#endif
        return true;
    }
    else
    {
        return false;
    }
}
