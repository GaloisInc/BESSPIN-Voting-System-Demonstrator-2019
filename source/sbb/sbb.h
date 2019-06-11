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

extern SBB_state the_state;

// @todo kiniry This is a placeholder state representation so that we
// can talk about the state of memory-mapped firmware.  It should
// probably be refined to a separate memory-mapped region (or more
// than one) per device and an invariant should stipulate that the
// memory regions are distinct.
typedef bool firmware_state;
extern firmware_state the_firmware_state;

// @design kiniry I am presuming that this function must be called
// prior to any other function and guarantees that all devices are put
// in their initial state.

// @design kiniry We could (should?) encode device driver/hardware
// subsystem state explicitly and state a separated clause between
// them here, something like
//   \separated(sd_card_dd_state, time_dd_state, etc.);

// @design kiniry All of these functions that are commands have a
// tight frame axiom, as they state exactly what part of `the_state`
// of the system is update, which is the model state for the SBB ASM.
// They must also explicitly state which mem-mapped state they modify
// in the implementation itself for compositional reasoning to be
// sound.

/*@ assigns the_firmware_state;
*/
// @todo Should immediately transition to `go_to_standby()`.
void initialize(void);

// @review kiniry ...for the election.
/*@ requires \valid(the_barcode + (0..its_length));
  @ assigns \nothing;
*/
bool is_barcode_valid(barcode the_barcode, barcode_length its_length);

/*@ assigns \nothing;
  @ ensures \result == (the_state.B == CAST_BUTTON_DOWN);
*/
bool is_cast_button_pressed(void);

/*@ assigns \nothing;
  @ ensures \result == (the_state.B == SPOIL_BUTTON_DOWN);
*/
bool is_spoil_button_pressed(void);

/*@ requires the_state.P == EARLY_AND_LATE_DETECTED;
  @ assigns \nothing;
  @ ensures \result == (the_state.BS == BARCODE_PRESENT_AND_RECORDED);
*/
bool has_a_barcode(void);

// @review kiniry Is the intention that this set of functions
// (just_received_barcode, set_received_barcode, and
// what_is_the_barcode) is the underlying (non-public) functions
// encoding the device driver/firmware for the barcode scanner
// subsystem?
/*@ requires \valid(the_barcode + (0..its_length));
  @ requires the_state.BS == BARCODE_PRESENT_AND_RECORDED;
*/
// assigns the_barcode + (0..its_length);
// ensures (* the model barcode is written to the_barcode *)
// @design kiniry Should this function return the number of bytes in
// the resulting barcode?
void what_is_the_barcode(barcode the_barcode, barcode_length its_length);

// @review kiniry We have no ASM for button light states.
/*@ assigns the_state.button_illumination;
  @ ensures spoil_button_lit(the_state);
*/
void spoil_button_light_on(void);

/*@ assigns the_state.button_illumination;
  @ ensures !spoil_button_lit(the_state);
*/
void spoil_button_light_off(void);

/*@ assigns the_state.button_illumination;
  @ ensures cast_button_lit(the_state);
*/
void cast_button_light_on(void);

/*@ assigns the_state.button_illumination;
  @ ensures !cast_button_lit(the_state);
*/
void cast_button_light_off(void);

/*@ assigns the_state.M;
  @ ensures the_state.M == MOTORS_TURNING_FORWARD;
*/
void move_motor_forward(void);

/*@ assigns the_state.M;
  @ ensures the_state.M == MOTORS_TURNING_BACKWARD;
*/
void move_motor_back(void);

/*@ assigns the_state.M;
  @ ensures the_state.M == MOTORS_OFF;
*/
void stop_motor(void);

// @design kiniry What is the memory map for the display?  We should
// be able to specify, both at the model and code level, what is on
// the display.
/*@ requires \valid_read(the_string_to_display + (0..its_length));
  @ assigns the_state.D;
  @ ensures the_state.D == SHOWING_TEXT;
*/
void display_this_text(char* the_string_to_display, uint8_t its_length);

/*@ assigns \nothing;
  @ ensures \result == (the_state.P == EARLY_PAPER_DETECTED);
*/
bool ballot_detected(void);

/*@ assigns \nothing;
  @ ensures \result == (the_state.P == EARLY_AND_LATE_DETECTED);
*/
bool ballot_inserted(void);

/*@ requires spoil_button_lit(the_state);
  @ requires the_state.P == EARLY_AND_LATE_DETECTED;
  @ assigns the_state.button_illumination,
  @         the_state.P;
  @ ensures no_buttons_lit(the_state);
  @ ensures the_state.P == NO_PAPER_DETECTED;
*/
void spoil_ballot(void);

/*@ requires cast_button_lit(the_state);
  @ requires the_state.P == EARLY_AND_LATE_DETECTED;
  @ assigns the_state.button_illumination,
  @         the_state.P;
  @ ensures no_buttons_lit(the_state);
  @ ensures the_state.P == NO_PAPER_DETECTED;
*/
void cast_ballot(void);

/*@ assigns the_state.P;
  @ ensures \result == the_state.P == EARLY_PAPER_DETECTED;
*/
bool ballot_spoiled(void);

// Semi-equivalent to initialize() without firmware initialization.
// @review Shouldn't calling this function clear the paper path?
/*@ assigns the_state.M, the_state.D, the_state.P, the_state.BS, the_state.S;
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.D == SHOWING_TEXT;
  @ ensures the_state.P == NO_PAPER_DETECTED;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
  @ ensures the_state.S == INNER;
  @ ensures no_buttons_lit(the_state);
*/
// @todo kiniry `insert_ballot_text` should be displayed.
void go_to_standby(void);

// @design kiniry These next four functions should also probably move
// out of this API, right Michal?

//@ assigns \nothing;
void ballot_detect_timeout_reset(void);

//@ assigns \nothing;
bool ballot_detect_timeout_expired(void);

//@ assigns \nothing;
void cast_or_spoil_timeout_reset(void);

//@ assigns \nothing;
bool cast_or_spoil_timeout_expired(void);

/*@ terminates \false;
    ensures \false;
*/
void ballot_box_main_loop(void);

#endif /* __SBB_H__ */
