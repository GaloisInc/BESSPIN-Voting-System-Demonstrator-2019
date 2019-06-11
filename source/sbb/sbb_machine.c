/**
 * Smart Ballot Box State Machine
 * @refine sbb.lando
 */

// General includes
#include <stdio.h>
#include <string.h>

// Subsystem includes
#include "sbb.h"
#include "sbb_t.h"
#include "sbb.acsl"

// Text defines (from sbb_main.c)
char *insert_ballot_text = "Insert ballot.";
char *barcode_detected_text = "Barcode detected.";
char *cast_or_spoil_text = "Cast or Spoil?";
char *casting_ballot_text = "Casting ballot.";
char *spoiling_ballot_text = "Spoiling ballot.";
char *not_a_valid_barcode_text = "Not a valid barcode!";
char *no_barcode_text = "No barcode detected!";
char *remove_ballot_text = "Remove ballot!";

SBB_state the_state = { .S = START };

// This main loop for the SBB never terminates until the system is
// turned off.
/*@ terminates \false;
  @ ensures    \false;
*/
void ballot_box_main_loop(void) {
  char this_barcode[BARCODE_MAX_LENGTH] = {0};
  // Set initial states
  the_state.L = STANDBY;
  go_to_standby();
  for(;;) {
    switch ( the_state.L ) {
    case STANDBY:
      go_to_Standby();
    case WAIT_FOR_BALLOT:
      if ( ballot_detected() ) {
        ballot_detect_timeout_reset();
        move_motor_forward();
        the_state.L = FEED_BALLOT;
      }
      break;

    case FEED_BALLOT:
      // Let the motor run. The next guard is the transition out of
      // this state: either we have a ballot with a barcode
      if ( ballot_inserted() || ballot_detect_timeout_expired() ) {
        stop_motor();
        if ( ballot_inserted() && has_a_barcode() ) {
          the_state.L = BARCODE_DETECTED;
        } else {
          the_state.L = WAIT_FOR_BALLOT;
        }
      }
      break;

    case BARCODE_DETECTED:
      // Assume: has_a_barcode() == true. Is this in sbb.h?
      what_is_the_barcode(this_barcode, BARCODE_MAX_LENGTH);
      if ( is_barcode_valid(this_barcode, BARCODE_MAX_LENGTH) ) {
        cast_button_light_on();
        spoil_button_light_on();
        cast_or_spoil_timeout_reset();
        the_state.L = BARCODE_VALIDATED;
      } else {
        the_state.L = SPOIL;
      }
      break;

    case BARCODE_VALIDATED:
      if (    cast_or_spoil_timeout_expired()
           || is_cast_button_pressed()
           || is_spoil_button_pressed() ) {
        spoil_button_light_off();
        cast_button_light_off();
        the_state.L = is_cast_button_pressed() ? CAST : SPOIL;
      }
      break;

    case CAST:
      cast_ballot();
      the_state.L = WAIT_FOR_BALLOT;
      break;

    case SPOIL:
      spoil_ballot();
      the_state.L = WAIT_FOR_SPOIL;
      break;

    case WAIT_FOR_SPOIL:
      if ( ballot_spoiled() ) {
        the_state.L = WAIT_FOR_BALLOT;
      }
      break;

      //default:
      //assert(false);
    }
  }
}

