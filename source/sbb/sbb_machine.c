/**
 * Smart Ballot Box State Machine
 * @refine sbb.lando
 */

// General includes
#include <stdio.h>
#include <string.h>

// SBB subsystem includes
#include "sbb.h"
#include "sbb_freertos.h"
#include "sbb.acsl"
// SBB private includes
#include "sbb_logging.h"
#include "sbb_machine.h"

#include <FreeRTOS.h>
#include <task.h>

// @design kiniry Here is the explicit encoding of the SBB state.
SBB_state the_state = { .S = START };

// @todo kiniry This is a placeholder state representation so that we
// can talk about the state of memory-mapped firmware.
firmware_state the_firmware_state;


void update_paper_state(bool paper_in_pressed,
                        bool paper_in_released)
{
    switch (the_state.P) {
    case NO_PAPER_DETECTED:
        if ( paper_in_pressed ) {
            CHANGE_STATE(the_state, P, PAPER_DETECTED);
        }
        break;

    case PAPER_DETECTED:
        if ( paper_in_released ) {
            CHANGE_STATE(the_state, P, NO_PAPER_DETECTED);
        }
        break;
    }
}

void update_button_state(bool cast_button_pressed,
                         bool cast_button_released,
                         bool spoil_button_pressed,
                         bool spoil_button_released) {
    switch ( the_state.B ) {
    default:
        break;
    case ALL_BUTTONS_UP:
        if ( cast_button_pressed ) {
            CHANGE_STATE(the_state, B, CAST_BUTTON_DOWN);
        } else if ( spoil_button_pressed ) {
            CHANGE_STATE(the_state, B, SPOIL_BUTTON_DOWN);
        }
        break;

    case CAST_BUTTON_DOWN:
        if ( cast_button_released ) {
            CHANGE_STATE(the_state, B, ALL_BUTTONS_UP);
        }
        break;

    case SPOIL_BUTTON_DOWN:
        if ( spoil_button_released ) {
            CHANGE_STATE(the_state, B, ALL_BUTTONS_UP);
        }
        break;
    }
}

/*@ requires \valid((char *)pvRxData + (0 .. xBufferLengthBytes-1));
  @ assigns *((char *)pvRxData + (0 .. \result - 1));
  @ ensures 0 <= \result;
  @ ensures \result <= xBufferLengthBytes;
*/
extern size_t xStreamBufferReceive(StreamBufferHandle_t xStreamBuffer,
                                   void *pvRxData,
                                   size_t xBufferLengthBytes,
                                   TickType_t xTicksToWait);

void update_barcode_state( bool barcode_scanned ) {
    switch ( the_state.BS ) {
    case BARCODE_NOT_PRESENT:
        if ( barcode_scanned ) {
            char barcode[BARCODE_MAX_LENGTH] = {0};
            barcode_length_t xReceiveLength = 0;
            xReceiveLength = xStreamBufferReceive(xScannerStreamBuffer,
                                                  barcode,
                                                  BARCODE_MAX_LENGTH,
                                                  SCANNER_BUFFER_RX_BLOCK_TIME_MS);
            if ( xReceiveLength > 0 ) {
                set_received_barcode(barcode, xReceiveLength);
                CHANGE_STATE(the_state, BS, BARCODE_PRESENT_AND_RECORDED);
            }
        }
        break;
    default:
        break;
    }
}

void flush_barcodes() {
    /*@ loop invariant SBB_Machine_Invariant;
      @ loop invariant the_state.L == ABORT || the_state.L == STANDBY;
      @ loop assigns the_state.BS, the_state.L, the_state.P,
      @ the_state.B, log_fs, barcode[0 .. BARCODE_MAX_LENGTH-1], barcode_length;
      @*/
    do {
        the_state.BS = BARCODE_NOT_PRESENT;
        update_sensor_state();
    } while (the_state.BS == BARCODE_PRESENT_AND_RECORDED);
}

// This refines the internal paper ASM event
//@ assigns \nothing;
EventBits_t next_paper_event_bits(void) {
    switch ( the_state.P ) {
    case NO_PAPER_DETECTED:
        return ebPAPER_SENSOR_IN_PRESSED;
    case PAPER_DETECTED:
        return ebPAPER_SENSOR_IN_RELEASED;
    default:
        break;
    }

    return 0;
}

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

EventBits_t next_barcode_event_bits(void) {
    switch ( the_state.BS ) {
    case BARCODE_NOT_PRESENT:
        return ebBARCODE_SCANNED;
    default:
        break;
    }

    return 0;
}

extern EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                       const EventBits_t uxBitsToSet );

void log_single_event( EventBits_t event_bits,
                       EventBits_t log_bit,
                       const char *event_entry,
                       int length ) {
    if ( event_bits & log_bit ) {
        if ( !log_system_message(event_entry, length) ) {
            debug_printf("Failed to write to system log.");
        }
    }
}

void log_event_group_result ( EventBits_t bits ) {
    log_single_event(bits, ebPAPER_SENSOR_IN_PRESSED, sensor_in_pressed_msg, strlen(sensor_in_pressed_msg));
    log_single_event(bits, ebPAPER_SENSOR_IN_RELEASED, sensor_in_released_msg, strlen(sensor_in_released_msg));

    log_single_event(bits, ebCAST_BUTTON_PRESSED, cast_button_pressed_msg, strlen(cast_button_pressed_msg));
    log_single_event(bits, ebCAST_BUTTON_RELEASED, cast_button_released_msg, strlen(cast_button_released_msg));
    log_single_event(bits, ebSPOIL_BUTTON_PRESSED, spoil_button_pressed_msg, strlen(spoil_button_pressed_msg));
    log_single_event(bits, ebSPOIL_BUTTON_RELEASED, spoil_button_released_msg, strlen(spoil_button_released_msg));

    log_single_event(bits, ebBARCODE_SCANNED, barcode_scanned_msg, strlen(barcode_scanned_msg));
}

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
    log_event_group_result(ux_Returned);

    /* "Run" the internal paper ASM transition */
    update_paper_state( (ux_Returned & ebPAPER_SENSOR_IN_PRESSED),
                        (ux_Returned & ebPAPER_SENSOR_IN_RELEASED) );

    /* "Run" the internal button ASM transition */
    update_button_state( (ux_Returned & ebCAST_BUTTON_PRESSED),
                         (ux_Returned & ebCAST_BUTTON_RELEASED),
                         (ux_Returned & ebSPOIL_BUTTON_PRESSED),
                         (ux_Returned & ebSPOIL_BUTTON_RELEASED) );

    /* "Run" the internal barcode ASM transition */
    update_barcode_state( (ux_Returned & ebBARCODE_SCANNED) );
}

void run_await_removal(void) {
    if ( !ballot_detected() ) {
        CHANGE_STATE(the_state, L, STANDBY);
    }
}

void run_eject(void) {
    eject_ballot();
    display_this_text(remove_ballot_text, strlen(remove_ballot_text));
    CHANGE_STATE(the_state, L, AWAIT_REMOVAL);
}

void run_spoil(void) {
    spoil_ballot();
    display_this_text(remove_ballot_text, strlen(remove_ballot_text));
    CHANGE_STATE(the_state, L, AWAIT_REMOVAL);
}

void run_cast(void) {
    display_this_text(casting_ballot_text,
                      strlen(casting_ballot_text));
    cast_ballot();
    CHANGE_STATE(the_state, L, STANDBY);
}

void run_wait_for_decision(void) {
    char this_barcode[BARCODE_MAX_LENGTH] = {0};
    barcode_length_t its_length;
    its_length = what_is_the_barcode(this_barcode);
    if ( cast_or_spoil_timeout_expired() ) {
        spoil_button_light_off();
        cast_button_light_off();
        log_system_message(decision_timeout_event_msg, strlen(decision_timeout_event_msg));
        CHANGE_STATE(the_state, L, EJECT);
    } else if ( is_cast_button_pressed() ) {
        if ( !log_app_event(APP_EVENT_BALLOT_USER_CAST,
                            this_barcode,
                            its_length) ) {
            debug_printf("Failed to write to app log.");
            CHANGE_STATE(the_state, L, ABORT);
        } else {
            CHANGE_STATE(the_state, L, CAST);
        }
    } else if ( is_spoil_button_pressed() ) {
        if ( !log_app_event(APP_EVENT_BALLOT_USER_SPOIL, this_barcode, its_length) ) {
            debug_printf("Failed to write to app log.");
            CHANGE_STATE(the_state, L, ABORT);
        } else {
            CHANGE_STATE(the_state, L, SPOIL);
        }
    } else {
        // pass
    }
}
void run_barcode_detected(void) {
    char this_barcode[BARCODE_MAX_LENGTH] = {0};
    display_this_text(barcode_detected_text,
                     strlen(barcode_detected_text));
    barcode_length_t length = what_is_the_barcode(this_barcode);
    if ( barcode_cast_or_spoiled(this_barcode, length) ) {
        // Eject Ballot
        display_this_2_line_text(duplicate_barcode_line_1_text,
                                 strlen(duplicate_barcode_line_1_text),
                                 duplicate_barcode_line_2_text,
                                 strlen(duplicate_barcode_line_2_text));
        debug_printf("previously seen barcode detected");
        CHANGE_STATE(the_state, L, EJECT);
    } else if ( is_barcode_valid(this_barcode, length) ) {
        // Prompt the user for a decision
        debug_printf("valid barcode detected");
        cast_button_light_on();
        spoil_button_light_on();
        cast_or_spoil_timeout_reset();
        display_this_2_line_text(cast_or_spoil_line_1_text,
                                 strlen(cast_or_spoil_line_1_text),
                                 cast_or_spoil_line_2_text,
                                 strlen(cast_or_spoil_line_2_text));
        // Go to the waiting state
        CHANGE_STATE(the_state, L, WAIT_FOR_DECISION);
    } else {
        debug_printf("invalid barcode detected");
        display_this_text(invalid_barcode_text,
                          strlen(invalid_barcode_text));
        log_system_message(invalid_barcode_received_event_msg,
                           strlen(invalid_barcode_received_event_msg));
        CHANGE_STATE(the_state, L, EJECT);
    }
}

void run_feed_ballot(void) {
    // We want to stop the motor if we've run it for too long
    // or if we no longer detect any paper. Then we see if we got a barcode
    // to determine which state to transition to.
    if ( !ballot_detected() || ballot_detect_timeout_expired() ) {
        stop_motor();
        if ( has_a_barcode() ) {
            CHANGE_STATE(the_state, L, BARCODE_DETECTED);
        } else {
            display_this_text(no_barcode_text, strlen(no_barcode_text));
            CHANGE_STATE(the_state, L, EJECT);
        }
    }
}

void run_wait_for_ballot(void) {
    if ( ballot_detected() ) {
        ballot_detect_timeout_reset();
        move_motor_forward();
        CHANGE_STATE(the_state, L, FEED_BALLOT);
    }
}

void run_initialize(void) {
    initialize();
    if ( LOG_FS_OK == Log_IO_Initialize() ) {
        if ( load_or_create_logs() ) {
            update_sensor_state();
            if ( ballot_detected() ) {
                CHANGE_STATE(the_state, L, EJECT);
            } else {
                CHANGE_STATE(the_state, L, STANDBY);
            }
        } else {
            debug_printf("Failed to import logs.");
            CHANGE_STATE(the_state, L, ABORT);
        }
    } else {
        debug_printf("Failed to initialize logging system.");
        CHANGE_STATE(the_state, L, ABORT);
    }
}

void run_standby(void) {
    flush_barcodes();
    go_to_standby();
    CHANGE_STATE(the_state, L, WAIT_FOR_BALLOT);
}

void run_abort(void) {
    display_this_2_line_text(error_line_1_text,
                             strlen(error_line_1_text),
                             error_line_2_text,
                             strlen(error_line_2_text));
}

/*@ requires SBB_Machine_Invariant;
  @ ensures SBB_Machine_Invariant;
*/
void take_step(void) {
    switch ( the_state.L ) {
    default:
        break;

    case STANDBY:
        run_standby();
        break;

    case WAIT_FOR_BALLOT:
        run_wait_for_ballot();
        break;

    case FEED_BALLOT:
        run_feed_ballot();
        break;

    case BARCODE_DETECTED:
        run_barcode_detected();
        break;

    case WAIT_FOR_DECISION:
        run_wait_for_decision();
        break;

    case CAST:
        run_cast();
        break;

    case SPOIL:
        run_spoil();
        break;

    case EJECT:
        run_eject();
        break;

    case AWAIT_REMOVAL:
        run_await_removal();
        break;

    case ABORT:
        run_abort();
        configASSERT(false);
        break;
        //default:
        //assert(false);
    }
}

// This exists to isolate the effect of the var_arg call (which we can't specify)
/*@ assigns \nothing; */
logic_state debug_state_change(logic_state then, logic_state now) {
    if (then != now) {
        debug_printf("logic state changed to %d", now);
    }
    return now;
}
// This main loop for the SBB never terminates until the system is
// turned off.
void ballot_box_main_loop(void) {
    the_state.L = INITIALIZE;
    logic_state old = 0;
    run_initialize();

    /*@ loop invariant SBB_Machine_Invariant;
     */
    for(;;) {
        debug_state_change(old, the_state.L);
        old = the_state.L;
        take_step();
        
        if (the_state.L != ABORT)
          update_sensor_state();
    }
}
