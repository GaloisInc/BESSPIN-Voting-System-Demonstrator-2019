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

typedef enum { UNKNOWN_CARD_STATE,
               CARD_READY } sd_card_state;
typedef enum { INITIALIZED=CARD_READY+1,
               RUNNING,
               STOPPED } timer_state;
typedef enum { MOTORS_OFF,
               MOTORS_TURNING_FORWARD,
               MOTORS_TURNING_BACKWARD} motor_state;
typedef enum { INITIALIZATION,
               INITIALIZED_DISPLAY,
               SHOWING_TEXT } display_state;
typedef enum { EARLY_PAPER_DETECTED,
               LATE_PAPER_DETECTED,
               EARLY_AND_LATE_DETECTED } paper_detect_state;
typedef enum { ALL_BUTTONS_UP,
               SPOIL_BUTTON_DOWN,
               CAST_BUTTON_DOWN } cast_spoil_state;
typedef enum { BARCODE_NOT_PRESENT,
               BARCODE_PRESENT_AND_RECORDED } barcode_scanner_state;
// @design kiniry START and STOP are the top-level (superposed) start
// and stop state for all ASMs.
typedef enum { START, STOP } background_state;

// sbb_state state;

#endif
