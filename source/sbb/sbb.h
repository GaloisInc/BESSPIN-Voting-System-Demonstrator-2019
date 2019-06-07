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
extern char *insert_ballot_text;
extern char *barcode_detected_text;
extern char *cast_or_spoil_text;
extern char *casting_ballot_text;
extern char *spoiling_ballot_text;
extern char *not_a_valid_barcode_text;
extern char *no_barcode_text;
extern char *remove_ballot_text;

/**
 * Initialize peripherals
 */
void initialize(void);

void perform_tabulation(void);

bool is_barcode_valid(barcode the_barcode, barcode_length its_length);

bool is_cast_button_pressed(void);

bool is_spoil_button_pressed(void);

bool has_a_barcode(void);

void just_received_barcode(void);

void set_received_barcode(barcode the_barcode, barcode_length its_length);

void what_is_the_barcode(barcode the_barcode, barcode_length its_length);

void spoil_button_light_on(void);

void spoil_button_light_off(void);

void cast_button_light_on(void);

void cast_button_light_off(void);

void move_motor_forward(void);

void move_motor_back(void);

void stop_motor(void);

void display_this_text(char *the_string_to_display, uint8_t its_length);

bool ballot_detected(void);

bool ballot_inserted(void);

void spoil_ballot(void);

void cast_ballot(void);

bool ballot_spoiled(void);

void go_to_standby(void);

void ballot_detect_timeout_reset(void);

bool ballot_detect_timeout_expired(void);

void cast_or_spoil_timeout_reset(void);

bool cast_or_spoil_timeout_expired(void);

/**
 * Main ballot box loop
 */
void ballot_box_main_loop(void);

#endif /* __SBB_H__ */
