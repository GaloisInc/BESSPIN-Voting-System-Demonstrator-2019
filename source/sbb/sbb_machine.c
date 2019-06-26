/**
 * Smart Ballot Box State Machine
 * @refine sbb.lando
 */

// General includes
#include <stdio.h>
#include <string.h>

// Subsystem includes
#include "sbb.h"
#include "sbb_freertos.h"
#include "sbb.acsl"

#include <FreeRTOS.h>
#include <task.h>

// @design kiniry Here is the explicit encoding of the SBB state.
SBB_state the_state = { .S = START };

// @todo kiniry This is a placeholder state representation so that we
// can talk about the state of memory-mapped firmware.
firmware_state the_firmware_state;

// @todo abakst refactor or expose this
extern void set_received_barcode(barcode_t the_barcode, barcode_length_t its_length);

// @todo abakst the ASM does not have NO_PAPER_DETECTED as reachable except from the initial
// state. Is this intentional?
/*@ assigns the_state.P;
  @ ensures \old(the_state.P) == the_state.P
  @      || ASM_transition(\old(the_state), INTERNAL_PAPER_DETECT_E, the_state);
*/
void update_paper_state(bool paper_in_pressed,
                        bool paper_in_released,
                        bool paper_out_pressed,
                        bool paper_out_released)
{
  switch (the_state.P) {
  case NO_PAPER_DETECTED:
    if ( paper_in_pressed ) {
      the_state.P = EARLY_PAPER_DETECTED;
    }
    break;

  case EARLY_PAPER_DETECTED:
    if ( paper_in_released && paper_out_pressed ) {
      the_state.P = LATE_PAPER_DETECTED;
    } else if ( paper_in_released ) {
      // see todo above
      the_state.P = NO_PAPER_DETECTED;
    } else if ( paper_out_pressed ) {
      the_state.P = EARLY_AND_LATE_DETECTED;
    }
    break;

  case LATE_PAPER_DETECTED:
    if ( paper_in_pressed && paper_out_released ) {
      the_state.P = EARLY_PAPER_DETECTED;
    } else if ( paper_in_pressed ) {
      the_state.P = EARLY_AND_LATE_DETECTED;
    } else if ( paper_out_released ) {
      // see todo above
      the_state.P = NO_PAPER_DETECTED;
    }
    break;

  case EARLY_AND_LATE_DETECTED:
    if ( paper_in_released && paper_out_released ) {
      // see todo above
      the_state.P = NO_PAPER_DETECTED;
    } else if ( paper_in_released ) { 
      the_state.P = LATE_PAPER_DETECTED;
    } else if ( paper_out_released ) {
      the_state.P = EARLY_PAPER_DETECTED;
    }
    break;
  }
}

/*@ assigns the_state.B;
  @ ensures \old(the_state) == the_state
  @      || ASM_transition(\old(the_state), INTERNAL_CAST_SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), CAST_E, the_state);
*/
void update_button_state(bool cast_button_pressed,
                         bool cast_button_released,
                         bool spoil_button_pressed,
                         bool spoil_button_released) {
  switch ( the_state.B ) {
  case ALL_BUTTONS_UP:
    if ( cast_button_pressed ) {
      the_state.B = CAST_BUTTON_DOWN;
    } else if ( spoil_button_pressed ) {
      the_state.B = SPOIL_BUTTON_DOWN;
    }
    break;

  case CAST_BUTTON_DOWN:
    if ( cast_button_released ) {
      the_state.B = ALL_BUTTONS_UP;
    }
    break;

  case SPOIL_BUTTON_DOWN:
    if ( spoil_button_released ) {
      the_state.B = ALL_BUTTONS_UP;
    }
    break;
  }
}

/*@ assigns the_state.BS;
  @ ensures \old(the_state) == the_state
  @      || ASM_transition(\old(the_state), INTERNAL_BARCODE_E, the_state);
*/
void update_barcode_state( bool barcode_scanned ) {
  switch ( the_state.BS ) {
  case BARCODE_NOT_PRESENT:
    if ( barcode_scanned ) {
      char barcode[BARCODE_MAX_LENGTH] = {0};
      barcode_length_t xReceiveLength = 0;
      xReceiveLength = xStreamBufferReceive(xScannerStreamBuffer,
                                            (void *)barcode, sizeof(barcode),
                                            SCANNER_BUFFER_RX_BLOCK_TIME_MS);
      if ( xReceiveLength > 0 ) {
        set_received_barcode(barcode, xReceiveLength);
        the_state.BS = BARCODE_PRESENT_AND_RECORDED;
      }
    }
    break;
  default:
    break;
  }
}

// This refines the internal paper ASM event
//@ assigns \nothing;
EventBits_t next_paper_event_bits(void) {
  switch ( the_state.P ) {
  case NO_PAPER_DETECTED:
    return (ebPAPER_SENSOR_IN_PRESSED);
  case EARLY_PAPER_DETECTED:
    return (ebPAPER_SENSOR_IN_RELEASED | ebPAPER_SENSOR_OUT_PRESSED);
  case LATE_PAPER_DETECTED:
    return (ebPAPER_SENSOR_IN_PRESSED | ebPAPER_SENSOR_OUT_RELEASED);
  case EARLY_AND_LATE_DETECTED:
    return (ebPAPER_SENSOR_IN_RELEASED | ebPAPER_SENSOR_OUT_RELEASED);
  default:
    break;
  }

  return 0;
}

// This refines the internal button ASM event
//@ assigns \nothing;
EventBits_t next_button_event_bits(void) {
  switch ( the_state.B ) {
  case ALL_BUTTONS_UP:
    return (ebCAST_BUTTON_PRESSED | ebSPOIL_BUTTON_PRESSED);
  case SPOIL_BUTTON_DOWN:
    return ebSPOIL_BUTTON_RELEASED;
  case CAST_BUTTON_DOWN:
    return ebCAST_BUTTON_RELEASED;
  default:
    break;
  }

  return 0;
}

//@ assigns \nothing;
EventBits_t next_barcode_event_bits(void) {
  switch ( the_state.BS ) {
  case BARCODE_NOT_PRESENT:
    return ebBARCODE_SCANNED;
  default:
    break;
  }

  return 0;
}

//@ assigns \nothing;
extern EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                       const EventBits_t uxBitsToSet );

/*@ ensures
  @ \exists SBB_state s1, SBB_state s2;
  @      (s1 == \old(the_state) || ASM_transition(\old(the_state), INTERNAL_PAPER_DETECT_E, s1))
  @      && (s2 == s1 || ASM_transition(s1, INTERNAL_CAST_SPOIL_E, s2)
  @                   || ASM_transition(\old(the_state), SPOIL_E, the_state)
  @                   || ASM_transition(\old(the_state), CAST_E, the_state))
  @      && (the_state == s2 || ASM_transition(s2, INTERNAL_BARCODE_E, the_state));
*/
void update_sensor_state(void) {
  EventBits_t waitEvents = 0;
  waitEvents |= next_paper_event_bits();
  waitEvents |= next_button_event_bits();
  waitEvents |= next_barcode_event_bits();
  if ( waitEvents == 0 ) {
	  return;
  }

  // @todo the demo has a timeout of 100msec when waiting for a barcode..does that matter?
  // @todo what about timer ASM? does that need to go here?
  EventBits_t ux_Returned =  xEventGroupWaitBits( xSBBEventGroup,
                                                  waitEvents,
                                                  pdTRUE,  /* Clear events on return        */
                                                  pdFALSE, /* Wait for *any* event, not all */
                                                  pdMS_TO_TICKS(100) ); 

  /* "Run" the internal paper ASM transition */
  update_paper_state( (ux_Returned & ebPAPER_SENSOR_IN_PRESSED),
                      (ux_Returned & ebPAPER_SENSOR_IN_RELEASED),
                      (ux_Returned & ebPAPER_SENSOR_OUT_PRESSED),
                      (ux_Returned & ebPAPER_SENSOR_OUT_RELEASED) );

  /* "Run" the internal button ASM transition */
  update_button_state( (ux_Returned & ebCAST_BUTTON_PRESSED),
                       (ux_Returned & ebCAST_BUTTON_RELEASED),
                       (ux_Returned & ebSPOIL_BUTTON_PRESSED),
                       (ux_Returned & ebSPOIL_BUTTON_RELEASED) );

  /* "Run" the internal barcode ASM transition */
  update_barcode_state( (ux_Returned & ebBARCODE_SCANNED) );
}

// This main loop for the SBB never terminates until the system is
// turned off.
/*@ terminates \false;
  @ ensures    \false;
*/
void ballot_box_main_loop(void) {
  char this_barcode[BARCODE_MAX_LENGTH] = {0};

  initialize();
  the_state.L = STANDBY;
  for(;;) {

    // Do internal transitions
    update_sensor_state();

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

      // Requires: motor is running forward
    case FEED_BALLOT:
      // The next guard is the transition out of
      // this state: either we have a ballot with a barcode
      // or we're out of time.
      if ( ballot_inserted() || has_a_barcode() || ballot_detect_timeout_expired() ) {
        stop_motor();
        if ( /* ballot_inserted()  && */ has_a_barcode() ) {
          the_state.L = BARCODE_DETECTED;
        } else {
          display_this_text(no_barcode_text, strlen(no_barcode_text));
          the_state.L = ERROR;
        }
      }
      break;

      // Requires: has_a_barcode
    case BARCODE_DETECTED:
      display_this_text(barcode_detected_text,
                        strlen(barcode_detected_text));
      what_is_the_barcode(this_barcode, BARCODE_MAX_LENGTH);
      if ( is_barcode_valid(this_barcode, BARCODE_MAX_LENGTH) ) {
        // Prompt the user for a decision
        cast_button_light_on();
        spoil_button_light_on();
        cast_or_spoil_timeout_reset();
        display_this_2_line_text(cast_or_spoil_line_1_text,
                                 strlen(cast_or_spoil_line_1_text),
                                 cast_or_spoil_line_2_text,
                                 strlen(cast_or_spoil_line_2_text));
        // Go to the waiting state
        the_state.L = WAIT_FOR_DECISION;
      } else {
        display_this_text(invalid_barcode_text,
                          strlen(invalid_barcode_text));
        the_state.L = ERROR;
      }
      break;

    case WAIT_FOR_DECISION:
      if ( cast_or_spoil_timeout_expired() ) {
        spoil_button_light_off();
        cast_button_light_off();
        the_state.L = ERROR;
      } else if ( is_cast_button_pressed() ) {
        the_state.L = CAST;
      } else if ( is_spoil_button_pressed() ) {
        the_state.L = SPOIL;
      }
      break;

    case CAST:
      display_this_text(casting_ballot_text,
                        strlen(casting_ballot_text));
      cast_ballot();
      the_state.L = STANDBY;
      break;

    case SPOIL:
      spoil_button_light_off();
      cast_button_light_off();
      display_this_text(spoiling_ballot_text,
                        strlen(spoiling_ballot_text));
      spoil_ballot();
      display_this_text(remove_ballot_text, strlen(remove_ballot_text));
      the_state.L = STANDBY;
      break;

    case ERROR:
      // abakst I think this needs a timeout & then head to an abort state?
      if ( ballot_inserted() || ballot_detected() ) {
        move_motor_back();
      } else {
        stop_motor();
        the_state.L = STANDBY;
      }
      break;

      //default:
      //assert(false);
    }
  }
}

