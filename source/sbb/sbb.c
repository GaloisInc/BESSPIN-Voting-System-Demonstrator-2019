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

#include "gpio.h"
#include "serLcd.h"

// Motor defines
#define MOTOR_0 4
#define MOTOR_1 5

// Timeouts
#define BALLOT_DETECT_TIMEOUT_MS 6000
#define CAST_OR_SPOIL_TIMEOUT_MS 30000

// Button defines
#define BUTTON_CAST_LED 1
#define BUTTON_SPOIL_LED 3
#define BUTTON_CAST_IN 0
#define BUTTON_SPOIL_IN 2

// Paper sensor inputs
#define PAPER_SENSOR_OUT 6
#define PAPER_SENSOR_IN 7

TickType_t ballot_detect_timeout = 0;
TickType_t cast_or_spoil_timeout = 0;

bool barcode_present = false;
char barcode[BARCODE_MAX_LENGTH] = {0};
SemaphoreHandle_t barcode_mutex;

/**
 * Initialize peripherals
 */
void init_sbb(void)
{
    gpio_set_as_input(BUTTON_CAST_IN);
    gpio_set_as_input(BUTTON_SPOIL_IN);
    gpio_set_as_input(PAPER_SENSOR_IN);
    gpio_set_as_input(PAPER_SENSOR_OUT);
    gpio_set_as_output(MOTOR_0);
    gpio_set_as_output(MOTOR_1);
    gpio_set_as_output(BUTTON_CAST_LED);
    gpio_set_as_output(BUTTON_SPOIL_LED);

    barcode_mutex = xSemaphoreCreateMutex();
}

/**
 * Perform Tally!
 */
void perform_tally(void) { printf("Performing tally\r\n"); }

/**
 * Is barcode valid?
 * Check validity of the given barcode string
 */
bool is_barcode_valid(char *str, uint8_t len)
{
    (void)str;
    (void)len;
    return true;
}

/**
 * Is Cast button pressed?
 */
bool is_cast_button_pressed(void) { return gpio_read(BUTTON_CAST_IN); }

/**
 * Is Spoil button pressed?
 */
bool is_spoil_button_pressed(void) { return gpio_read(BUTTON_SPOIL_IN); }

/**
 * Just received barcode!
 */
void just_received_barcode(void)
{
    if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE)
    {
        barcode_present = true;
        xSemaphoreGive(barcode_mutex);
    }
}

/**
 * Set barcode to this value
 */
void set_received_barcode(char *str, uint8_t len)
{
    configASSERT(len <= BARCODE_MAX_LENGTH);
    if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE)
    {
        memcpy(barcode, str, len);
        xSemaphoreGive(barcode_mutex);
    }
}

/**
 * Has a barcode?
 */
bool has_a_barcode(void)
{
    bool val = false;
    if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE)
    {
        val = barcode_present;
        xSemaphoreGive(barcode_mutex);
    }
    return val;
}

/**
 * What is the barcode?
 */
void what_is_the_barcode(char *str, uint8_t len)
{
    configASSERT(len <= BARCODE_MAX_LENGTH);
    if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE)
    {
        memcpy(str, barcode, len);
        xSemaphoreGive(barcode_mutex);
    }
}

/**
 * Spoil Button Light On!
 */
void spoil_button_light_on(void) { gpio_write(BUTTON_SPOIL_LED); }

/**
 * Spoil Button Light Off!
 */
void spoil_button_light_off(void) { gpio_clear(BUTTON_SPOIL_LED); }

/**
 * Cast Button Light On!
 */
void cast_button_light_on(void) { gpio_write(BUTTON_CAST_LED); }

/**
 * Cast Button Light Off!
 */
void cast_button_light_off(void) { gpio_clear(BUTTON_CAST_LED); }

/**
 * Move Motor Forward!
 */
void move_motor_forward(void)
{
    gpio_write(MOTOR_0);
    gpio_clear(MOTOR_1);
}

/**
 * Move Motor back!
 */
void move_motor_back(void)
{
    gpio_clear(MOTOR_0);
    gpio_write(MOTOR_1);
}

/**
 * Stop Motor!
 */
void stop_motor(void)
{
    gpio_clear(MOTOR_0);
    gpio_clear(MOTOR_1);
}

/**
 * Display this text!
 */
void display_this_text(char *str, uint8_t len) { serLcdPrintf(str, len); }

/**
 * Ballot detected?
 */
bool ballot_detected(void) { return gpio_read(PAPER_SENSOR_IN); }

/**
 * Ballot inserted?
 */
bool ballot_inserted(void) { return gpio_read(PAPER_SENSOR_OUT); }

/**
 * Spoil ballot!
 */
void spoil_ballot(void)
{
    move_motor_back();
    while (!(ballot_detected() && !ballot_inserted()))
    {
        ;
        ;
    }
    stop_motor();
}

/**
 * Cast ballot!
 */
void cast_ballot(void)
{
    move_motor_forward();
    while (!(!ballot_detected() && ballot_inserted()))
    {
        ;
        ;
    }
    stop_motor();
}

/**
 * Ballot spoiled?
 */
bool ballot_spoiled(void) { return (!ballot_detected() && !ballot_inserted()); }

/**
 * Go to standby!
 */
void go_to_standby(void)
{
    stop_motor();
    cast_button_light_off();
    spoil_button_light_off();
    display_this_text(insert_ballot_text, strlen(insert_ballot_text));
}

/**
 * Ballot Detect Timeout Reset!
 */
void ballot_detect_timeout_reset(void)
{
    ballot_detect_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(BALLOT_DETECT_TIMEOUT_MS);
}

/**
 * Ballot Detect Timeout Expired?
 */
bool ballot_detect_timeout_expired(void)
{
    return (xTaskGetTickCount() > ballot_detect_timeout);
}

/**
 * Cast Or Spoil Timeout Reset!
 */
void cast_or_spoil_timeout_reset(void)
{
    cast_or_spoil_timeout =
        xTaskGetTickCount() + pdMS_TO_TICKS(CAST_OR_SPOIL_TIMEOUT_MS);
}

/**
 * Cast Or Spoil Timeout Expired?
 */
bool cast_or_spoil_timeout_expired(void)
{
    return (xTaskGetTickCount() > cast_or_spoil_timeout);
}
