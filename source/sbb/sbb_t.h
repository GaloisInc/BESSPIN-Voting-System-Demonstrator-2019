/**
 * Smart Ballot Box types
 * @refine sbb.lando
 */

#ifndef __SBB_T__
#define __SBB_T__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#define BARCODE_MAX_LENGTH 16

typedef char* barcode;
// @todo kiniry Add a pure helper function for relating
// BARCODE_MAX_LENGTH to all uses of the pair (barcode,
// barcode_length).
typedef uint8_t barcode_length;
// @review kiniry Should we introduce a string type?
typedef char* string;

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
typedef enum { EARLY_PAPER_DETECTED = SHOWING_TEXT+1,
               LATE_PAPER_DETECTED,
               EARLY_AND_LATE_DETECTED } paper_detect_state;
typedef enum { ALL_BUTTONS_UP=EARLY_AND_LATE_DETECTED+1,
               SPOIL_BUTTON_DOWN,
               CAST_BUTTON_DOWN } buttons_state;
typedef enum { BARCODE_NOT_PRESENT = CAST_BUTTON_DOWN+1,
               BARCODE_PRESENT_AND_RECORDED } barcode_scanner_state;
// @design kiniry START and STOP are the top-level (superposed) start
// and stop state for all ASMs.
typedef enum { START = BARCODE_PRESENT_AND_RECORDED+1,
               STOP } start_stop_state;

// @design kiniry This is the record type that encodes the full
// top-level set of states for the SBB.  Note that a C record type for
// fields F, G encodes the tuple type (F, G) which is equivalent to
// the product type F x G.
typedef struct SBB_states {
  sd_card_state C;
  timer_state T;
  motor_state M;
  display_state D;
  paper_detect_state P;
  buttons_state B;
  start_stop_state S;
} SBB_state;

// @design kiniry Here is the explicit encoding of the SBB state.
SBB_state the_state;

#endif
