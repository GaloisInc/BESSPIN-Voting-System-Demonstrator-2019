/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */
#ifndef __SBB_H__
#define __SBB_H__

// General includes
#include <stdbool.h>
#include <stdint.h>

// Subsystem includes
#include "sbb_t.h"

// Aux
// @review kiniry Aren't these consts?
extern char *insert_ballot_text;
extern char *barcode_detected_text;
extern char *cast_or_spoil_text;
extern char *casting_ballot_text;
extern char *spoiling_ballot_text;
extern char *not_a_valid_barcode_text;
extern char *no_barcode_text;
extern char *remove_ballot_text;

void initialize(void);

/*@ requires \valid(the_barcode + (0..its_length));
  @ assigns \nothing;
*/
bool is_barcode_valid(barcode the_barcode, barcode_length its_length);

//@ assigns \nothing;
bool is_cast_button_pressed(void);

//@ assigns \nothing;
bool is_spoil_button_pressed(void);

//@ assigns \nothing;
bool has_a_barcode(void);

//@ assigns \nothing;
void just_received_barcode(void);

/*@ requires \valid(the_barcode + (0..its_length));
  @ assigns \nothing;
*/
void set_received_barcode(barcode the_barcode, barcode_length its_length);

/*@ requires \valid(the_barcode + (0..its_length));
  @ assigns \nothing;
*/
void what_is_the_barcode(barcode the_barcode, barcode_length its_length);

//@ assigns \nothing;
void spoil_button_light_on(void);


//@ assigns \nothing;
void spoil_button_light_off(void);

//@ assigns \nothing;
void cast_button_light_on(void);

//@ assigns \nothing;
void cast_button_light_off(void);

//@ assigns \nothing;
void move_motor_forward(void);

//@ assigns \nothing;
void move_motor_back(void);

//@ assigns \nothing;
void stop_motor(void);

/*@ requires \valid_read(the_string_to_display + (0..its_length));
  @ assigns \nothing;
*/
void display_this_text(char* the_string_to_display, uint8_t its_length);

//@ assigns \nothing;
bool ballot_detected(void);

//@ assigns \nothing;
bool ballot_inserted(void);

//@ assigns \nothing;
void spoil_ballot(void);

//@ assigns \nothing;
void cast_ballot(void);

//@ assigns \nothing;
bool ballot_spoiled(void);

//@ assigns \nothing;
void go_to_standby(void);

//@ assigns \nothing;
void ballot_detect_timeout_reset(void);

//@ assigns \nothing;
bool ballot_detect_timeout_expired(void);

//@ assigns \nothing;
void cast_or_spoil_timeout_reset(void);

//@ assigns \nothing;
bool cast_or_spoil_timeout_expired(void);

/**
 * Main ballot box loop
 */
void ballot_box_main_loop(void);

#endif /* __SBB_H__ */
