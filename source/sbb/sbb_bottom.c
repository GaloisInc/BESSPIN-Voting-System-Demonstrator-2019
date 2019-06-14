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

void perform_tabulation(void) {
  printf("Performing tabulation\r\n");
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

void just_received_barcode(void) {
  assert(false);
  //@ assert false;
}

void set_received_barcode(barcode_t the_barcode, barcode_length_t its_length) {
  assert(false);
  //@ assert false;
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

void display_this_text(char *str, uint8_t len) {
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


int main(void) {
  printf("Starting SBB...\r\n");
  ballot_box_main_loop();
}
