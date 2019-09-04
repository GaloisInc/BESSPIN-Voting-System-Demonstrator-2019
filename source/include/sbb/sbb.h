/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */
#ifndef __SBB_H__
#define __SBB_H__

#include "votingdefs.h"

// General includes
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

// Subsystem includes
#include "sbb_t.h"
#include "sbb.acsl"
#include "sbb_globals.h"
#include "sbb_logging.h"
#include "sbb_io_constants.h"
// Specs
#include "sbb_asm_prop.h"
#include "sbb_invariants.h"

/* Streaming Handles. */
extern osd_stream_buffer_handle_t xScannerStreamBuffer;

/* Event definitions. */
extern osd_event_group_handle_t xSBBEventGroup;
#define ebPAPER_SENSOR_IN_PRESSED  (0x01)
#define ebPAPER_SENSOR_IN_RELEASED (0x02)
#define ebBARCODE_SCANNED          (0x04)
#define ebCAST_BUTTON_PRESSED      (0x08)
#define ebCAST_BUTTON_RELEASED     (0x10)
#define ebSPOIL_BUTTON_PRESSED     (0x20)
#define ebSPOIL_BUTTON_RELEASED    (0x40)
#define ebALL_EVENTS               (0x7F)

// @todo kiniry This is a placeholder state representation so that we
// can talk about the state of memory-mapped firmware.  It should
// probably be refined to a separate memory-mapped region (or more
// than one) per device and an invariant should stipulate that the
// memory regions are distinct.
typedef bool firmware_state;
extern firmware_state the_firmware_state;

/*@ assigns \nothing;
    ensures \result == gpio_mem[i];
 */
uint8_t gpio_read(uint8_t i);

/*@ assigns gpio_mem[i];
    ensures gpio_mem[i] == 1;
 */
void    gpio_write(uint8_t i);

/*@ assigns gpio_mem[i];
    ensures gpio_mem[i] == 0;
 */
void    gpio_clear(uint8_t i);

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
/*@ requires log_not_init: !Log_IO_Initialized;
  @ requires state_is_init: the_state.L == INITIALIZE;
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.L == INITIALIZE;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
  @ ensures the_state.FS == LOG_OK;
  @ ensures the_state.P == NO_PAPER_DETECTED;
  @ ensures barcode_length == 0;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
  @ ensures \result == true || \result == false;
*/
bool initialize(void);

// @review kiniry Needs a postcondition that states that the currently
// held ballot is a legal ballot for the election, as soon as the crypto
// spec is ready for use.
/*@ requires \valid(the_barcode + (0 .. its_length - 1));
  @ assigns \nothing;
  @ ensures (\result == BARCODE_VALID) <==> Barcode_Valid(the_barcode, its_length);
*/
barcode_validity is_barcode_valid(barcode_t the_barcode, barcode_length_t its_length);

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
  @ requires the_state.BS == BARCODE_PRESENT_AND_RECORDED;
  @ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires \separated(the_barcode + (0 .. barcode_length - 1),
  @                     barcode     + (0 .. barcode_length - 1));
  @ assigns *(the_barcode + (0 .. barcode_length - 1));
  @ ensures barcode_length == \result;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
  @ ensures Barcode_Eq{Here,Here}(&barcode[0], the_barcode, \result);
*/
barcode_length_t what_is_the_barcode(barcode_t the_barcode);

// @review kiniry We have no ASM for button light states.
/*@ assigns the_state.button_illumination, gpio_mem[BUTTON_SPOIL_LED];
  @ ensures spoil_button_lit(the_state);
  @ ensures gpio_mem[BUTTON_SPOIL_LED] == 1;
  @ ensures cast_button_lit(the_state) <==> cast_button_lit(\old(the_state));
*/
void spoil_button_light_on(void);

/*@ assigns  the_state.button_illumination, gpio_mem[BUTTON_SPOIL_LED];
  @ ensures !spoil_button_lit(the_state);
  @ ensures gpio_mem[BUTTON_SPOIL_LED] == 0;
  @ ensures cast_button_lit(the_state) <==> cast_button_lit(\old(the_state));
*/
void spoil_button_light_off(void);

/*@ assigns the_state.button_illumination, gpio_mem[BUTTON_CAST_LED];
  @ ensures cast_button_lit(the_state);
  @ ensures gpio_mem[BUTTON_CAST_LED] == 1;
  @ ensures spoil_button_lit(the_state) <==> spoil_button_lit(\old(the_state));
*/
void cast_button_light_on(void);

/*@ assigns  the_state.button_illumination, gpio_mem[BUTTON_CAST_LED];
  @ ensures !cast_button_lit(the_state);
  @ ensures gpio_mem[BUTTON_CAST_LED] == 0;
  @ ensures spoil_button_lit(the_state) <==> spoil_button_lit(\old(the_state));
*/
void cast_button_light_off(void);

/*@ requires M_ASM_valid(the_state);
  @ requires Log_IO_Initialized;
  @ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L != ABORT;
  @ requires Paper_Present(the_state);
  @ requires the_state.L != AWAIT_REMOVAL;
  @ assigns the_state.M, the_state.FS, log_fs,
  @         gpio_mem[MOTOR_0],
  @         gpio_mem[MOTOR_1];
  @ ensures the_state.M == MOTORS_TURNING_FORWARD;
  @ ensures ASM_transition(\old(the_state), MOTOR_FORWARD_E, the_state);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void move_motor_forward(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires Paper_Present(the_state);
  @ requires the_state.L != AWAIT_REMOVAL;
  @ assigns the_state.M, the_state.FS, log_fs,
  @         gpio_mem[MOTOR_0],
  @         gpio_mem[MOTOR_1];
  @ ensures the_state.M == MOTORS_TURNING_BACKWARD;
  @ ensures gpio_mem[MOTOR_0] == 1;
  @ ensures gpio_mem[MOTOR_1] == 0;
  @ ensures ASM_transition(\old(the_state), MOTOR_BACKWARD_E, the_state);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
  @*/
void move_motor_back(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ assigns the_state.M, the_state.FS, log_fs,
            gpio_mem[MOTOR_0],
            gpio_mem[MOTOR_1];
  @ ensures gpio_mem[MOTOR_0] == 0;
  @ ensures gpio_mem[MOTOR_1] == 0;
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.M != \old(the_state.M) ==>
  @           ASM_transition(\old(the_state), MOTOR_OFF_E, the_state);
  @ ensures Log_IO_Initialized;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
  // The SBB Invariant may not be preserved, as we are changing the motor state, which is OK as
  // we can allow temporary invariant breakage during state transitions (which are not atomic).
*/
void stop_motor(void);

// @design kiniry What is the memory map for the display?  We should
// be able to specify, both at the model and code level, what is on
// the display.

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ assigns the_state.D, the_state.FS;
  @ assigns log_fs;
  @ ensures the_state.D == SHOWING_TEXT;
  @ ensures ASM_transition(\old(the_state), DISPLAY_TEXT_E, the_state);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void display_this_text(const char* the_text, uint8_t its_length);

void display_this_text_no_log(const char* the_text, uint8_t its_length);

void clear_display(void);

/*@ requires valid_read_string(line_1);
  @ requires valid_read_string(line_2);
  @ requires D_ASM_valid(the_state);
  @ requires FS_ASM_valid(the_state);
  @ requires Log_IO_Initialized;
  @ assigns the_state.D, the_state.FS;
  @ assigns log_fs;
  @ ensures the_state.D == SHOWING_TEXT;
  @ ensures ASM_transition(\old(the_state), DISPLAY_TEXT_E, the_state);
  @ ensures D_ASM_valid(the_state);
  @ ensures FS_ASM_valid(the_state);
  @ ensures Log_IO_Initialized;
*/
void display_this_2_line_text(const char *line_1, uint8_t length_1,
                              const char *line_2, uint8_t length_2);

/*@ assigns \nothing;
  @ ensures \result == (the_state.P == PAPER_DETECTED);
  @ ensures \result == true || \result == false;
*/
bool ballot_detected(void);

/*@ requires Paper_Present(the_state);
  @ requires the_state.L \in \union(SPOIL, EJECT);
  @ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires Paper_Present(the_state);
  @ assigns the_state.M, the_state.FS, log_fs,
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1];
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void eject_ballot(void);

/*@ requires the_state.L == SPOIL;
  @ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ assigns the_state.button_illumination, log_fs,
  @         gpio_mem[BUTTON_CAST_LED], gpio_mem[BUTTON_SPOIL_LED],
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1],
  @         the_state.FS, the_state.M, the_state.D;
  @ ensures no_buttons_lit(the_state);
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures the_state.D == SHOWING_TEXT;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void spoil_ballot(void);

/*@ requires the_state.L == CAST;
  @ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ assigns log_fs,
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1],
  @         the_state.M, the_state.FS, log_fs;
  @ ensures the_state.M == MOTORS_OFF;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void cast_ballot(void);

// Semi-equivalent to initialize() without firmware initialization.
// @review Shouldn't calling this function clear the paper path?
// @todo kiniry `insert_ballot_text` should be displayed.
/*@ requires valid_read_string(insert_ballot_text);
  @ requires valid_read_string(welcome_text);
  @ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ assigns the_state.M, the_state.D, the_state.P, the_state.BS, the_state.S, the_state.L,
  @         the_state.B, the_state.FS,
  @         the_state.button_illumination, log_fs,
  @         gpio_mem[BUTTON_CAST_LED], gpio_mem[BUTTON_SPOIL_LED],
  @         gpio_mem[MOTOR_0], gpio_mem[MOTOR_1];
  @ ensures the_state.L == STANDBY;
  @ ensures the_state.M  == MOTORS_OFF;
  @ ensures the_state.D  == SHOWING_TEXT;
  @ ensures the_state.P  == NO_PAPER_DETECTED;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
  @ ensures the_state.B  == ALL_BUTTONS_UP;
  @ ensures the_state.S  == INNER;
  @ ensures no_buttons_lit(the_state);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
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

/*@ requires !Log_IO_Initialized;
  @ terminates \false;
  @ ensures    \false;
*/
void ballot_box_main_loop(void);

/**
 * Get current system time
 * @return true if the time was retrieved correctly
 * @return false otherwise
 */
/*@ requires \valid(year);
  @ requires \valid(month);
  @ requires \valid(day);
  @ requires \valid(hour);
  @ requires \valid(minute);
  @ requires \separated(month, day);
  @ requires \separated(month, hour);
  @ requires \separated(month, minute);
  @ requires \separated(day, hour);
  @ requires \separated(day, minute);
  @ requires \separated(hour, minute);
  @ assigns *year, *month, *day, *hour, *minute;
  @ ensures \result == true || \result == false;
*/
bool get_current_time(uint32_t *year, uint16_t *month, uint16_t *day,
                      uint16_t *hour, uint16_t *minute);

#endif /* __SBB_H__ */
