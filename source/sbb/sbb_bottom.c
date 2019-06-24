/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

void initialize(void) {
  ;
}

bool is_barcode_valid(barcode_t the_barcode, barcode_length_t its_length) {
  assert(false);
  //@ assert false;
  return false;
}

bool is_cast_button_pressed(void) {
  assert(false);
  //@ assert false;
  return false;
}

bool is_spoil_button_pressed(void) {
  assert(false);
  //@ assert false;
  return false;
}

bool has_a_barcode(void) {
  assert(false);
  //@ assert false;
  return false;
}

void what_is_the_barcode(barcode_t the_barcode, barcode_length_t its_length) {
  assert(false);
  //@ assert false;
}

void spoil_button_light_on(void) {
  assert(false);
  //@ assert false;
}

void spoil_button_light_off(void) {
  assert(false);
  //@ assert false;
}

void cast_button_light_on(void) {
  assert(false);
  //@ assert false;
}

void cast_button_light_off(void) {
  assert(false);
  //@ assert false;
}

void move_motor_forward(void) {
  assert(false);
  //@ assert false;
}

void move_motor_back(void) {
  assert(false);
  //@ assert false;
}

void stop_motor(void) {
  assert(false);
  //@ assert false;
}

void display_this_text(const char *the_text, uint8_t its_length) {
  assert(false);
  //@ assert false;
}

void display_this_2_line_text(const char *line_1, uint8_t length_1, 
                              const char *line_2, uint8_t length_2) {
  assert(false);
  //@ assert false;
}
                              
bool ballot_detected(void) {
  assert(false);
  //@ assert false;
  return false;
}

bool ballot_inserted(void) {
  assert(false);
  //@ assert false;
  return false;
}

void spoil_ballot(void) {
  assert(false);
  //@ assert false;
}

void cast_ballot(void) {
  assert(false);
  //@ assert false;
}

bool ballot_spoiled(void) {
  assert(false);
  //@ assert false;
  return false;
}

void go_to_standby(void) {
  assert(false);
  //@ assert false;
}

void ballot_detect_timeout_reset(void) {
  assert(false);
  //@ assert false;
}

bool ballot_detect_timeout_expired(void) {
  assert(false);
  //@ assert false;
  return false;
}

void cast_or_spoil_timeout_reset(void) {
  assert(false);
  //@ assert false;
}

bool cast_or_spoil_timeout_expired(void) {
  assert(false);
  //@ assert false;
  return false;
}

void ballot_box_main_loop(void) {
  assert(false);
  //@ assert false;
}

int main(void) {
  printf("Starting SBB...\r\n");
  ballot_box_main_loop();
}
