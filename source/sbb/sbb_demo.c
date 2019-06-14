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
// BESSPIN Voting System devices
#include "gpio.h"
#include "serLcd.h"

/* Motor defines */
#define MOTOR_0 4
#define MOTOR_1 5

/* Timeouts */
#define BALLOT_DETECT_TIMEOUT_MS 6000
#define CAST_OR_SPOIL_TIMEOUT_MS 30000


/**
 * Initialize peripherals
 */
void init_sbb(void)
{
    gpio_set_as_output(MOTOR_0);
    gpio_set_as_output(MOTOR_1);
    gpio_set_as_output(BUTTON_CAST_LED);
    gpio_set_as_output(BUTTON_SPOIL_LED);
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

void perform_tabulation(void) { printf("Performing tabulation!\r\n"); }

bool is_barcode_valid(barcode_t the_barcode, barcode_length_t its_length) {
  (void)the_barcode;
  (void)its_length;
  return true;
}

bool is_cast_button_pressed(void) {
  return gpio_read(BUTTON_CAST_IN);
}

bool is_spoil_button_pressed(void) {
  bool pressed = gpio_read(BUTTON_CAST_IN);
  the_state.B  = pressed ? SPOIL_BUTTON_DOWN : the_state.B;
  return pressed;
}

/**
 * Just received barcode!
 */
void just_received_barcode(void)
{
    ;;
}

/**
 * Set barcode to this value
 */
void set_received_barcode(char *str, uint8_t len)
{
    ;;
}

/**
 * Has a barcode?
 */
bool has_a_barcode(void)
{
    return false;
}

/**
 * What is the barcode?
 */
void what_is_the_barcode(char *str, uint8_t len)
{
    ;;
}

void spoil_button_light_on(void) { gpio_write(BUTTON_SPOIL_LED); }

void spoil_button_light_off(void) { gpio_clear(BUTTON_SPOIL_LED); }

void cast_button_light_on(void) { gpio_write(BUTTON_CAST_LED); }

void cast_button_light_off(void) { gpio_clear(BUTTON_CAST_LED); }

/**
 * Move Motor Forward!
 */
void move_motor_forward(void)
{
    gpio_clear(MOTOR_0);
    gpio_write(MOTOR_1);
}

/**
 * Move Motor back!
 */
void move_motor_back(void)
{
    gpio_write(MOTOR_0);
    gpio_clear(MOTOR_1);
}

void stop_motor(void) {
  gpio_clear(MOTOR_0);
  gpio_clear(MOTOR_1);
  the_state.M = MOTORS_OFF;
}

void display_this_text(char *str, uint8_t len) {
  serLcdPrintf(str, len);
}

/**
 * Ballot detected?
 */
bool ballot_detected(void) { return !gpio_read(PAPER_SENSOR_IN); }

/**
 * Ballot inserted?
 */
bool ballot_inserted(void) { return !gpio_read(PAPER_SENSOR_OUT); }

/**
 * Spoil ballot!
 */
void spoil_ballot(void)
{
    cast_button_light_off();
    spoil_button_light_off();
    move_motor_back();
    for(;;) {
        if (!ballot_inserted() && ballot_detected()) {
            printf("Ready to remove paper\r\n");
            break;
        }
    }
    stop_motor();
}

/**
 * Cast ballot!
 */
void cast_ballot(void)
{
    cast_button_light_off();
    spoil_button_light_off();
    move_motor_forward();
    for(;;) {
        if (!ballot_inserted()) {
            printf("Casted?\r\n");
            break;
        }
    }
    stop_motor();
}

bool ballot_spoiled(void) { return (!ballot_detected() && !ballot_inserted()); }

void go_to_standby(void) {
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
    ;
}

/**
 * Ballot Detect Timeout Expired?
 */
bool ballot_detect_timeout_expired(void)
{
    return false;
}

/**
 * Cast Or Spoil Timeout Reset!
 */
void cast_or_spoil_timeout_reset(void)
{
    ;;
}

/**
 * Cast Or Spoil Timeout Expired?
 */
bool cast_or_spoil_timeout_expired(void)
{
    return false;
}
