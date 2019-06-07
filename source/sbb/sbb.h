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
void init_sbb(void);

/**
 * Perform Tally!
 */
void perform_tally(void);

/**
 * Is barcode valid?
 * Check validity of the given barcode string
 */
bool is_barcode_valid(barcode the_barcode, barcode_length its_length);

/**
 * Is Cast button pressed?
 */
bool is_cast_button_pressed(void);

/**
 * Is Spoil button pressed?
 */
bool is_spoil_button_pressed(void);

/**
 * Has a barcode?
 */
bool has_a_barcode(void);

/**
 * Just received barcode!
 */
void just_received_barcode(void);

/**
 * Set barcode to this value
 */
void set_received_barcode(barcode the_barcode, barcode_length its_length);

/**
 * What is the barcode?
 */
void what_is_the_barcode(barcode the_barcode, barcode_length its_length);

/**
 * Spoil Button Light On!
 */
void spoil_button_light_on(void);

/**
 * Spoil Button Light Off!
 */
void spoil_button_light_off(void);

/**
 * Cast Button Light On!
 */
void cast_button_light_on(void);

/**
 * Cast Button Light Off!
 */
void cast_button_light_off(void);

/**
 * Move Motor Forward!
 */
void move_motor_forward(void);

/**
 * Move Motor back!
 */
void move_motor_back(void);

/**
 * Stop Motor!
 */
void stop_motor(void);

/**
 * Display this text!
 */
void display_this_text(char *the_string_to_display, uint8_t its_length);

/**
 * Ballot detected?
 */
bool ballot_detected(void);

/**
 * Ballot inserted?
 */
bool ballot_inserted(void);

/**
 * Spoil ballot!
 */
void spoil_ballot(void);

/**
 * Cast ballot!
 */
void cast_ballot(void);

/**
 * Ballot spoiled?
 */
bool ballot_spoiled(void);

/**
 * Go to standby!
 */
void go_to_standby(void);

/**
 * Ballot Detect Timeout Reset!
 */
void ballot_detect_timeout_reset(void);

/**
 * Ballot Detect Timeout Expired?
 */
bool ballot_detect_timeout_expired(void);

/**
 * Cast Or Spoil Timeout Reset!
 */
void cast_or_spoil_timeout_reset(void);

/**
 * Cast Or Spoil Timeout Expired?
 */
bool cast_or_spoil_timeout_expired(void);

/**
 * Main ballot box loop
 */
void ballot_box_main_loop(void);

#endif /* __SBB_H__ */
