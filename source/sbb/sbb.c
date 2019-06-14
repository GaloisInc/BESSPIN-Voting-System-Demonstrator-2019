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

// BESSPIN Voting System devices
#include "gpio.h"
#include "serLcd.h"

// Timeouts
#define BALLOT_DETECT_TIMEOUT_MS 6000
#define CAST_OR_SPOIL_TIMEOUT_MS 30000

// Buttons
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


void initialize(void) {
  gpio_set_as_input(BUTTON_CAST_IN);
  gpio_set_as_input(BUTTON_SPOIL_IN);
  gpio_set_as_input(PAPER_SENSOR_IN);
  gpio_set_as_input(PAPER_SENSOR_OUT);
  gpio_set_as_output(MOTOR_0);
  gpio_set_as_output(MOTOR_1);
  gpio_set_as_output(BUTTON_CAST_LED);
  gpio_set_as_output(BUTTON_SPOIL_LED);
  
  barcode_mutex = xSemaphoreCreateMutex();
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

void just_received_barcode(void) {
  if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE) {
    barcode_present = true;
    xSemaphoreGive(barcode_mutex);
  }
}

void set_received_barcode(barcode_t the_barcode, barcode_length_t its_length) {
  configASSERT(its_length <= BARCODE_MAX_LENGTH);
  if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE) {
    memcpy(barcode, the_barcode, its_length);
    xSemaphoreGive(barcode_mutex);
  }
}

bool has_a_barcode(void) {
  bool val = false;
  if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE) {
    val = barcode_present;
    xSemaphoreGive(barcode_mutex);
  }
  return val;
}

void what_is_the_barcode(barcode_t the_barcode, barcode_length_t its_length) {
  configASSERT(its_length <= BARCODE_MAX_LENGTH);
  if (xSemaphoreTake(barcode_mutex, portMAX_DELAY) == pdTRUE) {
    memcpy(the_barcode, barcode, its_length);
    xSemaphoreGive(barcode_mutex);
  }
}

void spoil_button_light_on(void) { gpio_write(BUTTON_SPOIL_LED); }

void spoil_button_light_off(void) { gpio_clear(BUTTON_SPOIL_LED); }

void cast_button_light_on(void) { gpio_write(BUTTON_CAST_LED); }

void cast_button_light_off(void) { gpio_clear(BUTTON_CAST_LED); }

void move_motor_forward(void) {
  gpio_write(MOTOR_0);
  gpio_clear(MOTOR_1);
  the_state.M = MOTORS_TURNING_FORWARD;
}

void move_motor_back(void) {
  gpio_clear(MOTOR_0);
  gpio_write(MOTOR_1);
  the_state.M = MOTORS_TURNING_BACKWARD;
}

void stop_motor(void) {
  gpio_clear(MOTOR_0);
  gpio_clear(MOTOR_1);
  the_state.M = MOTORS_OFF;
}

void display_this_text(char *str, uint8_t len) {
  serLcdPrintf(str, len);
}

bool ballot_detected(void) { return gpio_read(PAPER_SENSOR_IN); }

bool ballot_inserted(void) {
  return gpio_read(PAPER_SENSOR_OUT);
}

void spoil_ballot(void) {
  move_motor_back();
  while (!(ballot_detected() && !ballot_inserted())) {
    ;
  }
  stop_motor();
}

void cast_ballot(void) {
  move_motor_forward();
  while (!(!ballot_detected() && ballot_inserted())) {
    ;
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

void ballot_detect_timeout_reset(void) {
  ballot_detect_timeout =
    xTaskGetTickCount() + pdMS_TO_TICKS(BALLOT_DETECT_TIMEOUT_MS);
}

bool ballot_detect_timeout_expired(void) {
  return (xTaskGetTickCount() > ballot_detect_timeout);
}

void cast_or_spoil_timeout_reset(void) {
  cast_or_spoil_timeout =
    xTaskGetTickCount() + pdMS_TO_TICKS(CAST_OR_SPOIL_TIMEOUT_MS);
}

bool cast_or_spoil_timeout_expired(void) {
  return (xTaskGetTickCount() > cast_or_spoil_timeout);
}
