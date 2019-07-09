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
#include "sbb_freertos.h"
#include "sbb_logging.h"
#include "sbb_crypto.h"

// BESSPIN Voting System devices
#include "gpio.h"
#include "serLcd.h"

// Timeouts
#define BALLOT_DETECT_TIMEOUT_MS 10000
#define CAST_OR_SPOIL_TIMEOUT_MS 30000
#define SPOIL_EJECT_TIMEOUT_MS 6000
#define CAST_INGEST_TIMEOUT_MS 6000

TickType_t ballot_detect_timeout = 0;
TickType_t cast_or_spoil_timeout = 0;

bool barcode_present = false;
char barcode[BARCODE_MAX_LENGTH] = {0};
barcode_length_t barcode_length  = 0;
SemaphoreHandle_t barcode_mutex;

// Assigns declarations for FreeRTOS functions; these may not be
// accurate but are currently required to avoid crashing wp.

//@ assigns \nothing;
extern void serLcdPrintf(char *str, uint8_t len);
//@ assigns \nothing;
extern void serLcdPrintTwoLines(char* line_1, uint8_t len_1, char* line_2, uint8_t len_2);
//@ assigns \nothing;
extern size_t xStreamBufferReceive(StreamBufferHandle_t xStreamBuffer,
                                   void *pvRxData,
                                   size_t xBufferLengthBytes,
                                   TickType_t xTicksToWait);
//@ assigns \nothing;
extern EventBits_t xEventGroupWaitBits(EventGroupHandle_t xEventGroup,
                                       const EventBits_t uxBitsToWaitFor,
                                       const BaseType_t xClearOnExit,
                                       const BaseType_t xWaitForAllBits,
                                       TickType_t xTicksToWait);

// main code

void initialize(void) {
    gpio_set_as_input(BUTTON_CAST_IN);
    gpio_set_as_input(BUTTON_SPOIL_IN);
    gpio_set_as_input(PAPER_SENSOR_IN);
    gpio_set_as_input(PAPER_SENSOR_OUT);
    gpio_set_as_output(MOTOR_0);
    gpio_set_as_output(MOTOR_1);
    gpio_set_as_output(BUTTON_CAST_LED);
    gpio_set_as_output(BUTTON_SPOIL_LED);
    the_state.button_illumination = 0;
 DevicesInitialized: return;
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

bool is_barcode_valid(barcode_t the_barcode, barcode_length_t its_length) {
    return crypto_check_barcode_valid(the_barcode, its_length);
}

bool is_cast_button_pressed(void) {
    return the_state.B == CAST_BUTTON_DOWN;
}

bool is_spoil_button_pressed(void) {
    return the_state.B == SPOIL_BUTTON_DOWN;
}

void just_received_barcode(void) {
}

void set_received_barcode(barcode_t the_barcode, barcode_length_t its_length) {
    configASSERT(its_length <= BARCODE_MAX_LENGTH);
    memcpy(barcode, the_barcode, its_length);
    barcode_length = its_length;
}

bool has_a_barcode(void) {
    return the_state.BS == BARCODE_PRESENT_AND_RECORDED;
}

barcode_length_t what_is_the_barcode(barcode_t the_barcode) {
    configASSERT(barcode_length > 0);
    memcpy(the_barcode, barcode, barcode_length);
    return barcode_length;
}

void spoil_button_light_on(void) {
    gpio_write(BUTTON_SPOIL_LED);
    the_state.button_illumination |= spoil_button_mask;
}

void spoil_button_light_off(void) {
    gpio_clear(BUTTON_SPOIL_LED);
    the_state.button_illumination &= ~spoil_button_mask;
}

void cast_button_light_on(void) {
    gpio_write(BUTTON_CAST_LED);
    the_state.button_illumination |= cast_button_mask;
}

void cast_button_light_off(void) {
    gpio_clear(BUTTON_CAST_LED);
    the_state.button_illumination &= ~cast_button_mask;
}

void move_motor_forward(void) {
    gpio_clear(MOTOR_0);
    gpio_write(MOTOR_1);
    CHANGE_STATE(the_state, M, MOTORS_TURNING_FORWARD);
}

void move_motor_back(void) {
    gpio_write(MOTOR_0);
    gpio_clear(MOTOR_1);
    CHANGE_STATE(the_state, M, MOTORS_TURNING_BACKWARD);
}

void stop_motor(void) {
    gpio_clear(MOTOR_0);
    gpio_clear(MOTOR_1);
    CHANGE_STATE(the_state, M, MOTORS_OFF);
}


void display_this_text(const char *the_text, uint8_t its_length) {
    #ifdef SIMULATION
    debug_printf("DISPLAY: %s\r\n", the_text);
    #else
    CHANGE_STATE(the_state,D,SHOWING_TEXT);
    serLcdPrintf(the_text, its_length);
    #endif
}

void display_this_2_line_text(const char *line_1, uint8_t length_1,
                              const char *line_2, uint8_t length_2) {
    #ifdef SIMULATION
    debug_printf("DISPLAY: %s\r\nLINETWO: %s\r\n", line_1, line_2);
    #else
    CHANGE_STATE(the_state,D,SHOWING_TEXT);
    serLcdPrintTwoLines(line_1, length_1, line_2, length_2);
    #endif
}

bool ballot_detected(void) {
    return (the_state.P == PAPER_DETECTED);
}

void eject_ballot(void) {
    move_motor_back();
    // run the motor for a bit to get the paper back over the switch
    TickType_t spoil_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(SPOIL_EJECT_TIMEOUT_MS);
    /*@ loop assigns \nothing; */
    while (xTaskGetTickCount() < spoil_timeout) {
        // wait for the motor to run a while
    }

    stop_motor();
}

void spoil_ballot(void) {
    spoil_button_light_off();
    cast_button_light_off();
    display_this_text(spoiling_ballot_text,
                      strlen(spoiling_ballot_text));
    eject_ballot();
}

void cast_ballot(void) {
    cast_button_light_off();
    move_motor_forward();

    // run the motor for a bit to get the paper into the box
    TickType_t cast_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(CAST_INGEST_TIMEOUT_MS);
    /*@ loop assigns \nothing; */
    while (xTaskGetTickCount() < cast_timeout) {
        // wait for the motor to run a while
    }

    stop_motor();
}

void go_to_standby(void) {
    if ( the_state.M != MOTORS_OFF ) {
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
void ballot_detect_timeout_reset(void) {
    ballot_detect_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(BALLOT_DETECT_TIMEOUT_MS);
}

bool ballot_detect_timeout_expired(void) {
    return (xTaskGetTickCount() > ballot_detect_timeout);
}

//@ assigns cast_or_spoil_timeout;
void cast_or_spoil_timeout_reset(void) {
    cast_or_spoil_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(CAST_OR_SPOIL_TIMEOUT_MS);
}

bool cast_or_spoil_timeout_expired(void) {
    return (xTaskGetTickCount() > cast_or_spoil_timeout);
}
