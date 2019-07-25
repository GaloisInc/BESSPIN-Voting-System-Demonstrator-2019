/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */
#ifndef __SBB_H__
#define __SBB_H__

// General includes
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

// Subsystem includes
#include "sbb_t.h"
#include "sbb.acsl"
#include "sbb_logging.h"

extern char barcode[BARCODE_MAX_LENGTH];
extern barcode_length_t barcode_length;

// Per-ballot-box data
extern const char *sbb_name; // to be prepended to log names
extern const uint8_t sbb_mac_address[6]; // for DHCP
extern const uint8_t sbb_default_ip_address[4]; // in case DHCP doesn't work
extern const uint8_t sbb_default_netmask[4]; // in case DHCP doesn't work
extern const uint8_t sbb_default_gateway_address[4]; // in case DHCP doesn't work
extern const uint8_t sbb_default_dns_server_address[4]; // in case DHCP doesn't work

// Display strings
extern const char *welcome_text;
extern const char *insert_ballot_text;
extern const char *barcode_detected_text;
extern const char *cast_or_spoil_line_1_text;
extern const char *cast_or_spoil_line_2_text;
extern const char *casting_ballot_text;
extern const char *spoiling_ballot_text;
extern const char *invalid_barcode_text;
extern const char *duplicate_barcode_line_1_text;
extern const char *duplicate_barcode_line_2_text;
extern const char *no_barcode_text;
extern const char *remove_ballot_text;
extern const char *error_line_1_text;
extern const char *error_line_2_text;

extern SBB_state the_state;

/*@ axiomatic SBB {

  predicate SBB_String(char *s) =
    0 < strlen(s) && strlen(s) <= 255 && valid_read_string(s);

  predicate SBB_Strings_Invariant =
    SBB_String(welcome_text) &&
    SBB_String(insert_ballot_text) &&
    SBB_String(barcode_detected_text) &&
    SBB_String(cast_or_spoil_line_1_text) &&
    SBB_String(cast_or_spoil_line_2_text) &&
    SBB_String(casting_ballot_text) &&
    SBB_String(spoiling_ballot_text) &&
    SBB_String(invalid_barcode_text) &&
    SBB_String(no_barcode_text) &&
    SBB_String(remove_ballot_text) &&
    SBB_String(error_line_1_text) &&
    SBB_String(error_line_2_text) &&
    SBB_String(sensor_in_pressed_msg) &&
    SBB_String(sensor_in_released_msg) &&
    SBB_String(sensor_out_pressed_msg) &&
    SBB_String(sensor_out_released_msg) &&
    SBB_String(cast_button_pressed_msg) &&
    SBB_String(cast_button_released_msg) &&
    SBB_String(spoil_button_pressed_msg) &&
    SBB_String(spoil_button_released_msg) &&
    SBB_String(barcode_scanned_msg) &&
    SBB_String(barcode_received_event_msg) &&
    SBB_String(empty_barcode_received_event_msg) &&
    SBB_String(invalid_barcode_received_event_msg) &&
    SBB_String(decision_timeout_event_msg) &&
    SBB_String(duplicate_barcode_line_1_text) &&
    SBB_String(duplicate_barcode_line_2_text) &&
    SBB_String(system_log_file_name) &&
    SBB_String(app_log_file_name);
}
*/

/*@ predicate SBB_Invariant =
  @   SBB_Strings_Invariant &&
  @   Log_IO_Initialized    &&
  @   0 <= barcode_length && barcode_length <= BARCODE_MAX_LENGTH &&
  @   Valid_ASM_States(the_state);
  @
  @ predicate SBB_Machine_Invariant =
  @   SBB_Invariant &&
  @   SBB_States_Invariant(the_state) &&
  @  (Barcode_Present(the_state) ==> barcode_length > 0);
*/

// @todo kiniry This is a placeholder state representation so that we
// can talk about the state of memory-mapped firmware.  It should
// probably be refined to a separate memory-mapped region (or more
// than one) per device and an invariant should stipulate that the
// memory regions are distinct.
typedef bool firmware_state;
extern firmware_state the_firmware_state;

// @spec abakst Specifications needed for for hardware, related to the
// above I think we probably want some ghost `uint8_t` array to model
// these reads/writes.
extern uint8_t gpio_mem[8];

/* Button defines */
#define BUTTON_CAST_LED 3
#define BUTTON_SPOIL_LED 1
#define BUTTON_CAST_IN 2
#define BUTTON_SPOIL_IN 0

/* Paper sensor inputs */
#define PAPER_SENSOR_OUT 6
#define PAPER_SENSOR_IN 7

// Motor defines
#define MOTOR_0 4
#define MOTOR_1 5

/*@ assigns \nothing; */
uint8_t gpio_read(uint8_t i);

/*@ assigns gpio_mem[i]; */
void    gpio_write(uint8_t i);

/*@ assigns gpio_mem[i]; */
void    gpio_clear(uint8_t i);


// This is temporary, to get around frama-c issues
// with strings. This is sound as long as:
// 1. none of our constant strings alias,
// 2. all of the strings actually satisfy SBB_String
/*@ assigns \nothing;
  @ ensures SBB_Strings_Invariant;
*/
void __assume_strings_OK(void);

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

// @todo Should immediately transition to `go_to_standby()`.
// @assurance kiniry The implementation of `initialize` must have a
// the C label `DevicesInitialized` on its final statement.
/*@ requires Log_IO_Initialized;
  @ requires the_state.L == INITIALIZE;
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.L == INITIALIZE;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
  @ ensures no_buttons_lit(the_state);
  @ ensures barcode_length == 0;
  @ ensures Log_IO_Initialized;
  @ ensures SBB_Strings_Invariant;
  @ ensures Valid_ASM_States(the_state);
*/
void initialize(void);

// @review kiniry Needs a postcondition that states that the currently
// held ballot is a legal ballot for the election, as soon as the crypto
// spec is ready for use.
/*@ requires \valid(the_barcode + (0 .. its_length - 1));
  @ assigns \nothing;
  @ ensures \result == true || \result == false;
*/
bool is_barcode_valid(barcode_t the_barcode, barcode_length_t its_length);

/*@ requires \valid_read(the_barcode);
  @ requires \valid_read(the_barcode + (1..its_length-1));
  @ requires its_length <= BARCODE_MAX_LENGTH;
  @ assigns barcode[0 .. its_length-1];
  @ assigns barcode_length;
  @ ensures barcode_length == its_length;
*/
void set_received_barcode(barcode_t the_barcode, barcode_length_t its_length);

/*@ assigns \nothing;
  @ ensures \result == (the_state.B == CAST_BUTTON_DOWN);
  @ ensures \result == true || \result == false;
*/
bool is_cast_button_pressed(void);

/*@ assigns \nothing;
  @ ensures \result == (the_state.B == SPOIL_BUTTON_DOWN);
  @ ensures \result == true || \result == false;
*/
bool is_spoil_button_pressed(void);

/*@ assigns \nothing;
  @ ensures \result == (the_state.BS == BARCODE_PRESENT_AND_RECORDED);
  @ ensures \result == true || \result == false;
*/
bool has_a_barcode(void);

// @review kiniry Is the intention that this set of functions
// (just_received_barcode, set_received_barcode, and
// what_is_the_barcode) is the underlying (non-public) functions
// encoding the device driver/firmware for the barcode scanner
// subsystem?
// ensures (* the model barcode is written to the_barcode *)
// @design kiniry Should this function return the number of bytes in
// the resulting barcode?
/*@ requires \valid(the_barcode + (0 .. BARCODE_MAX_LENGTH-1));
  @ requires \valid_read(barcode + (0 .. barcode_length-1));
  @ requires 0 < barcode_length && barcode_length <= BARCODE_MAX_LENGTH;
  @ requires the_state.BS == BARCODE_PRESENT_AND_RECORDED;
  @ requires SBB_Invariant;
  @ assigns *(the_barcode + (0 .. barcode_length - 1));
  @ ensures barcode_length == \result;
  @ ensures SBB_Invariant;
*/
barcode_length_t what_is_the_barcode(barcode_t the_barcode);

// @review kiniry We have no ASM for button light states.
/*@ assigns the_state.button_illumination, gpio_mem[BUTTON_SPOIL_LED];
  @ ensures spoil_button_lit(the_state);
  @ ensures cast_button_lit(the_state) <==> cast_button_lit(\old(the_state));
*/
void spoil_button_light_on(void);

/*@ assigns  the_state.button_illumination, gpio_mem[BUTTON_SPOIL_LED];
  @ ensures !spoil_button_lit(the_state);
  @ ensures cast_button_lit(the_state) <==> cast_button_lit(\old(the_state));
*/
void spoil_button_light_off(void);

/*@ assigns the_state.button_illumination, gpio_mem[BUTTON_CAST_LED];
  @ ensures cast_button_lit(the_state);
  @ ensures spoil_button_lit(the_state) <==> spoil_button_lit(\old(the_state));
*/
void cast_button_light_on(void);

/*@ assigns  the_state.button_illumination, gpio_mem[BUTTON_CAST_LED];
  @ ensures !cast_button_lit(the_state);
  @ ensures spoil_button_lit(the_state) <==> spoil_button_lit(\old(the_state));
*/
void cast_button_light_off(void);

/*@ requires M_ASM_valid(the_state);
  @ requires Log_IO_Initialized;
  @ requires the_state.M != MOTORS_TURNING_BACKWARD;
  @ assigns the_state.M, the_state.L, log_fs,
  @         gpio_mem[MOTOR_0],
  @         gpio_mem[MOTOR_1];
  @ ensures the_state.L == ABORT || the_state.L == \old(the_state).L;
  @ ensures the_state.M == MOTORS_TURNING_FORWARD;
  @ ensures ASM_transition(\old(the_state), MOTOR_FORWARD_E, the_state);
*/
void move_motor_forward(void);

/*@ requires M_ASM_valid(the_state);
  @ requires Log_IO_Initialized;
  @ requires the_state.M != MOTORS_TURNING_FORWARD;
  @ assigns the_state.M, the_state.L, log_fs,
  @         gpio_mem[MOTOR_0],
  @         gpio_mem[MOTOR_1];
  @ ensures the_state.M == MOTORS_TURNING_BACKWARD;
  @ ensures the_state.L == ABORT || the_state.L == \old(the_state.L);
  @ ensures ASM_transition(\old(the_state), MOTOR_BACKWARD_E, the_state);
  @*/
void move_motor_back(void);

/*@ requires M_ASM_valid(the_state);
  @ requires Log_IO_Initialized;
  @ assigns the_state.M, the_state.L, log_fs,
            gpio_mem[MOTOR_0],
            gpio_mem[MOTOR_1];
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.L == ABORT || the_state.L == \old(the_state.L);
  @ ensures the_state.M != \old(the_state.M) ==>
  @           ASM_transition(\old(the_state), MOTOR_OFF_E, the_state);
*/
void stop_motor(void);

// @design kiniry What is the memory map for the display?  We should
// be able to specify, both at the model and code level, what is on
// the display.

/*@ requires valid_read_string(the_text);
  @ requires D_ASM_valid(the_state);
  @ requires Log_IO_Initialized;
  @ assigns the_state.D, the_state.L;
  @ assigns log_fs;
  @ ensures the_state.D == SHOWING_TEXT;
  @ ensures the_state.L == \old(the_state.L) || the_state.L == ABORT;
  @ ensures ASM_transition(\old(the_state), DISPLAY_TEXT_E, the_state);
*/
void display_this_text(const char* the_text, uint8_t its_length);

/*@ requires valid_read_string(line_1);
  @ requires valid_read_string(line_2);
  @ requires D_ASM_valid(the_state);
  @ assigns the_state.D, the_state.L;
  @ assigns log_fs;
  @ ensures the_state.D == SHOWING_TEXT;
  @ ensures the_state.L == \old(the_state).L || the_state.L == ABORT;
  @ ensures ASM_transition(\old(the_state), DISPLAY_TEXT_E, the_state);
*/
void display_this_2_line_text(const char *line_1, uint8_t length_1,
                              const char *line_2, uint8_t length_2);

/*@ assigns \nothing;
  @ ensures \result == (the_state.P == PAPER_DETECTED);
  @ ensures \result == true || \result == false;
*/
bool ballot_detected(void);

/*@ requires the_state.M == MOTORS_OFF;
  @ assigns the_state.M, the_state.L, log_fs,
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1];
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.L == ABORT || the_state.L == \old(the_state).L;
*/
void eject_ballot(void);

/*@ requires the_state.M == MOTORS_OFF;
  @ requires D_ASM_valid(the_state);
  @ requires valid_read_string(spoiling_ballot_text);
  @ assigns the_state.button_illumination, log_fs,
  @         gpio_mem[BUTTON_CAST_LED], gpio_mem[BUTTON_SPOIL_LED],
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1],
  @         the_state.L, the_state.M, the_state.D;
  @ ensures no_buttons_lit(the_state);
  @ ensures the_state.L != ABORT ==> the_state.L == \old(the_state.L);
  @ ensures the_state.D == SHOWING_TEXT;
  @ ensures the_state.M == MOTORS_OFF;
*/
void spoil_ballot(void);

/*@ requires the_state.M == MOTORS_OFF;
  @ requires D_ASM_valid(the_state);
  @ assigns the_state.button_illumination,
  @         gpio_mem[BUTTON_SPOIL_LED], gpio_mem[BUTTON_CAST_LED],
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1],
  @         the_state.M, the_state.L, log_fs;
  @ ensures no_buttons_lit(the_state);
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.L == ABORT || the_state.L == \old(the_state.L);
*/
void cast_ballot(void);

// Semi-equivalent to initialize() without firmware initialization.
// @review Shouldn't calling this function clear the paper path?
// @todo kiniry `insert_ballot_text` should be displayed.
/*@ requires M_ASM_valid(the_state);
  @ requires D_ASM_valid(the_state);
  @ requires valid_read_string(insert_ballot_text);
  @ requires valid_read_string(welcome_text);
  @ assigns the_state.M, the_state.D, the_state.P, the_state.BS, the_state.S, the_state.L,
  @         the_state.B, the_state.button_illumination, log_fs,
  @         gpio_mem[BUTTON_CAST_LED], gpio_mem[BUTTON_SPOIL_LED],
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1];
  @ ensures the_state.L  == ABORT || the_state.L == STANDBY;
  @ ensures the_state.M  == MOTORS_OFF;
  @ ensures the_state.D  == SHOWING_TEXT;
  @ ensures the_state.P  == NO_PAPER_DETECTED;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
  @ ensures the_state.B  == ALL_BUTTONS_UP;
  @ ensures the_state.S  == INNER;
  @ ensures no_buttons_lit(the_state);
*/
void go_to_standby(void);

// @design kiniry These next four functions should also probably move
// out of this API, right Michal?

void ballot_detect_timeout_reset(void);

/*@ assigns \nothing;
  @ ensures \result == true || \result == false;
 */
bool ballot_detect_timeout_expired(void);

void cast_or_spoil_timeout_reset(void);

/*@ assigns \nothing;
  @ ensures \result == true || \result == false;
*/
bool cast_or_spoil_timeout_expired(void);

/*@ terminates \false;
  @ ensures    \false;
*/
void ballot_box_main_loop(void);

#endif /* __SBB_H__ */
