/**
 * Smart Ballot Box State Machine
 * @refine sbb.lando
 */

// General includes
#include <stdio.h>
#include <string.h>

// Subsystem includes
#include "sbb.h"
#include "sbb.acsl"

// Text defines
char *insert_ballot_text = "Insert ballot.";
char *barcode_detected_text = "Barcode detected.";
char *cast_or_spoil_text = "Cast or Spoil?";
char *casting_ballot_text = "Casting ballot.";
char *spoiling_ballot_text = "Spoiling ballot.";
char *not_a_valid_barcode_text = "Not a valid barcode!";
char *no_barcode_text = "No barcode detected!";
char *remove_ballot_text = "Remove ballot!";

// @design kiniry Here is the explicit encoding of the SBB state.
SBB_state the_state = { .S = START };

// @todo kiniry This is a placeholder state representation so that we
// can talk about the state of memory-mapped firmware.
firmware_state the_firmware_state;

// This main loop for the SBB never terminates until the system is
// turned off.
/*@ terminates \false;
  @ ensures    \false;
*/
void ballot_box_main_loop(void) {
  char this_barcode[BARCODE_MAX_LENGTH] = {0};
  for(;;) {
    // Set initial states
    switch ( the_state.L ) {

    case STANDBY:
      go_to_standby();
      the_state.L = WAIT_FOR_BALLOT;
      break;

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
          display_this_text(no_barcode_text, strlen(no_barcode_text));
          the_state.L = SPOIL;
        }
      }
      break;

    // Assume: has_a_barcode() == true. Is this in sbb.h?
    case BARCODE_DETECTED:
      display_this_text(barcode_detected_text,
                        strlen(barcode_detected_text));
      what_is_the_barcode(this_barcode, BARCODE_MAX_LENGTH);
      if ( is_barcode_valid(this_barcode, BARCODE_MAX_LENGTH) ) {
        cast_button_light_on();
        spoil_button_light_on();
        cast_or_spoil_timeout_reset();

        display_this_text(cast_or_spoil_text,
                          strlen(cast_or_spoil_text));
        the_state.L = BARCODE_VALIDATED;
      } else {
        display_this_text(not_a_valid_barcode_text,
                          strlen(not_a_valid_barcode_text));
        the_state.L = SPOIL;
      }
      break;

    case BARCODE_VALIDATED:
      if (    cast_or_spoil_timeout_expired()
           || is_cast_button_pressed()
           || is_spoil_button_pressed() ) {
        spoil_button_light_off();
        cast_button_light_off();
        if ( is_cast_button_pressed() ) {
          display_this_text(casting_ballot_text,
                            strlen(casting_ballot_text));
          the_state.L = CAST;
        } else {
          the_state.L = SPOIL;
        }
      }
      break;

    case CAST:
      cast_ballot();
      the_state.L = WAIT_FOR_BALLOT;
      break;

    case SPOIL:
      display_this_text(spoiling_ballot_text,
                        strlen(spoiling_ballot_text));
      spoil_ballot();
      display_this_text(remove_ballot_text, strlen(remove_ballot_text));
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

