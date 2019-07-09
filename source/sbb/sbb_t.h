/**
 * Smart Ballot Box types
 * @refine sbb.lando
 */

#ifndef __SBB_T__
#define __SBB_T__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#define BARCODE_MAX_LENGTH 254

typedef uint8_t* barcode_t;
// @todo kiniry Add a pure helper function for relating
// BARCODE_MAX_LENGTH to all uses of the pair (barcode,
// barcode_length).
typedef uint8_t barcode_length_t;
// @review kiniry Should we introduce a string type?
typedef char* string_t;

// @todo kiniry State names must be extracted from ASMs.

// @design kiniry Note that, due to how C enums work, we have to
// couple these definitions together to ensure that values are
// distinct.  This means that ordering of declaration matters, so
// please do not re-order these typedefs.

typedef enum { UNKNOWN_SD_CARD_STATE,
               SD_CARD_READY } sd_card_state;
typedef enum { INITIALIZED = SD_CARD_READY+1,
               RUNNING,
               STOPPED } timer_state;
typedef enum { MOTORS_OFF = STOPPED+1,
               MOTORS_TURNING_FORWARD,
               MOTORS_TURNING_BACKWARD} motor_state;
typedef enum { INITIALIZATION = MOTORS_TURNING_BACKWARD+1,
               INITIALIZED_DISPLAY,
               SHOWING_TEXT } display_state;
typedef enum { NO_PAPER_DETECTED = SHOWING_TEXT+1,
               PAPER_DETECTED } paper_detect_state;
typedef enum { ALL_BUTTONS_UP=PAPER_DETECTED+1,
               SPOIL_BUTTON_DOWN,
               CAST_BUTTON_DOWN } buttons_state;
typedef enum { BARCODE_NOT_PRESENT = CAST_BUTTON_DOWN+1,
               BARCODE_PRESENT_AND_RECORDED } barcode_scanner_state;
typedef enum { INITIALIZE = BARCODE_PRESENT_AND_RECORDED+1,
               STANDBY,
               WAIT_FOR_BALLOT,
               FEED_BALLOT,
               BARCODE_DETECTED,
               WAIT_FOR_DECISION,
               CAST,
               SPOIL,
               EJECT,
               AWAIT_REMOVAL,
               ABORT,
} logic_state;
// @design kiniry START and STOP are the top-level (superposed) start
// and stop state for all ASMs.
typedef enum { START = ABORT+1,
               INNER,
               STOP } start_stop_state;

// @design kiniry The following defines all events that can trigger an
// ASM state change in the SBB.
typedef enum { //motor_ASM
              MOTOR_OFF_E = STOP+1,
              MOTOR_FORWARD_E,
              MOTOR_BACKWARD_E,
              //sd_card_ASM
              CARD_PRESENT_E,
              ERASE_CARD_E,
              //barcode_ASM
              INTERNAL_BARCODE_E,
              //display_ASM
              INTERNAL_DISPLAY_E,
              DISPLAY_TEXT_E,
              //paper_detect_ASM
              INTERNAL_PAPER_DETECT_E,
              //cast_spoil_ASM
              SPOIL_E,
              CAST_E,
              INTERNAL_CAST_SPOIL_E,
              //timer_ASM
              INTERNAL_TIMER_E,
              TIMER_TICK_UNDER_E,
              TIMER_TICK_OVER_E,
              RESET_TIMER_E,
} SBB_event;

// @design kiniry This is the record type that encodes the full
// top-level set of states for the SBB.  Note that a C record type for
// fields F, G encodes the tuple type (F, G) which is equivalent to
// the product type F x G.
// @design kiniry Note that we would normally specify this as a model
// variable of this datatype, but Frama-C does not yet suppport model
// variables.  If we did have model variables, we would only have a
// concrete instance of this type for the SBB hardware emulator build.
typedef struct SBB_states {
    sd_card_state C;
    timer_state T;
    motor_state M;
    display_state D;
    paper_detect_state P;
    buttons_state B;
    barcode_scanner_state BS;
    start_stop_state S;
    logic_state L;
    // @design kiniry We encode button illumination state with a 2 bit
    // wide struct bitfield.  This encoding will help test our clang and
    // secure complication of such an out-of-the-ordinary C construct.
    uint8_t button_illumination: 2;
} SBB_state;

#define cast_button_mask  (0x1 << 0)
#define spoil_button_mask (0x1 << 1)

#define cast_button_lit(s) (s.button_illumination & cast_button_mask)
#define spoil_button_lit(s) (s.button_illumination & spoil_button_mask)
#define no_buttons_lit(s) !(cast_button_lit(s) || spoil_button_lit(s))

#endif
