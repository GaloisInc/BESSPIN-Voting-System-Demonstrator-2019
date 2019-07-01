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

// @todo abakst refactor or expose this
extern void set_received_barcode(barcode_t the_barcode, barcode_length_t its_length);

void update_paper_state(bool paper_in_pressed,
                        bool paper_in_released)
{
    switch (the_state.P) {
    case NO_PAPER_DETECTED:
        if ( paper_in_pressed ) {
<<<<<<< HEAD
            CHANGE_STATE(the_state, P, EARLY_PAPER_DETECTED);
        }
        break;

    case EARLY_PAPER_DETECTED:
        if ( paper_in_released && paper_out_pressed ) {
            CHANGE_STATE(the_state, P, LATE_PAPER_DETECTED);
        } else if ( paper_in_released ) {
            // see todo above
            CHANGE_STATE(the_state, P, NO_PAPER_DETECTED);
        } else if ( paper_out_pressed ) {
            CHANGE_STATE(the_state, P, EARLY_AND_LATE_DETECTED);
        }
        break;

    case LATE_PAPER_DETECTED:
        if ( paper_in_pressed && paper_out_released ) {
            CHANGE_STATE(the_state, P, EARLY_PAPER_DETECTED);
        } else if ( paper_in_pressed ) {
            CHANGE_STATE(the_state, P, EARLY_AND_LATE_DETECTED);
        } else if ( paper_out_released ) {
            // see todo above
            CHANGE_STATE(the_state, P, NO_PAPER_DETECTED);
        }
        break;

    case EARLY_AND_LATE_DETECTED:
        if ( paper_in_released && paper_out_released ) {
            // see todo above
            CHANGE_STATE(the_state, P, NO_PAPER_DETECTED);
        } else if ( paper_in_released ) {
            CHANGE_STATE(the_state, P, LATE_PAPER_DETECTED);
        } else if ( paper_out_released ) {
            CHANGE_STATE(the_state, P, EARLY_PAPER_DETECTED);
=======
            CHANGE_STATE(the_state, P, PAPER_DETECTED);
        }
        break;

    case PAPER_DETECTED:
        if ( paper_in_released ) {
            CHANGE_STATE(the_state, P, NO_PAPER_DETECTED);
>>>>>>> Remove SBB references to second paper sensor.
        }
        break;
    }
}

void update_button_state(bool cast_button_pressed,
                         bool cast_button_released,
                         bool spoil_button_pressed,
                         bool spoil_button_released) {
    switch ( the_state.B ) {
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
                CHANGE_STATE(the_state, BS, BARCODE_PRESENT_AND_RECORDED);
            }
        }
        break;
    default:
        break;
    }
}

// this is a workaround for multiple barcodes being "queued"
void flush_barcodes() {
    while (the_state.BS == BARCODE_PRESENT_AND_RECORDED) {
        the_state.BS = BARCODE_NOT_PRESENT;
        update_sensor_state();
    }
}

// This refines the internal paper ASM event
//@ assigns \nothing;
EventBits_t next_paper_event_bits(void) {
    switch ( the_state.P ) {
    case NO_PAPER_DETECTED:
<<<<<<< HEAD
        return (ebPAPER_SENSOR_IN_PRESSED);
    case EARLY_PAPER_DETECTED:
        return (ebPAPER_SENSOR_IN_RELEASED | ebPAPER_SENSOR_OUT_PRESSED);
    case LATE_PAPER_DETECTED:
        return (ebPAPER_SENSOR_IN_PRESSED | ebPAPER_SENSOR_OUT_RELEASED);
    case EARLY_AND_LATE_DETECTED:
        return (ebPAPER_SENSOR_IN_RELEASED | ebPAPER_SENSOR_OUT_RELEASED);
=======
        return ebPAPER_SENSOR_IN_PRESSED;
    case PAPER_DETECTED:
        return ebPAPER_SENSOR_IN_RELEASED;
>>>>>>> Remove SBB references to second paper sensor.
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


void log_single_event( EventBits_t bits,
                       EventBits_t bit,
                       const log_entry event_entry ) {
    if ( bits && bit ) {
        log_system_message(event_entry);
    }
}

void log_event_group_result ( EventBits_t bits ) {
    log_single_event(bits, ebPAPER_SENSOR_IN_PRESSED, sensor_in_pressed_msg);
    log_single_event(bits, ebPAPER_SENSOR_IN_RELEASED, sensor_in_released_msg);

    log_single_event(bits, ebCAST_BUTTON_PRESSED, cast_button_pressed_msg);
    log_single_event(bits, ebCAST_BUTTON_RELEASED, cast_button_released_msg);
    log_single_event(bits, ebSPOIL_BUTTON_PRESSED, spoil_button_pressed_msg);
    log_single_event(bits, ebSPOIL_BUTTON_RELEASED, spoil_button_released_msg);

    log_single_event(bits, ebBARCODE_SCANNED, barcode_scanned_msg);
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

// This main loop for the SBB never terminates until the system is
// turned off.
void ballot_box_main_loop(void) {
    char this_barcode[BARCODE_MAX_LENGTH] = {0};
    the_state.L = INITIALIZE;
    logic_state old = 0;

    for(;;) {
        if (the_state.L != old) {
            debug_printf("logic state changed to %d", the_state.L);
            old = the_state.L;
        }

        switch ( the_state.L ) {

        case INITIALIZE:
            initialize();
            Log_FS_Result logresult = Log_IO_Initialize();
            if ( logresult != LOG_FS_OK ) {
                CHANGE_STATE(the_state, L, ABORT);
            } else {
                load_or_create_logs();
                CHANGE_STATE(the_state, L, STANDBY);
            }
            break;

        case STANDBY:
            go_to_standby();
            flush_barcodes();
            CHANGE_STATE(the_state, L, WAIT_FOR_BALLOT);
            break;

        case WAIT_FOR_BALLOT:
            if ( ballot_detected() ) {
                ballot_detect_timeout_reset();
                move_motor_forward();
                CHANGE_STATE(the_state, L, FEED_BALLOT);
            }
            break;

        case FEED_BALLOT:
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
            break;

            // Requires: has_a_barcode
        case BARCODE_DETECTED:
            display_this_text(barcode_detected_text,
                              strlen(barcode_detected_text));
            what_is_the_barcode(this_barcode, BARCODE_MAX_LENGTH);
            if ( is_barcode_valid(this_barcode, BARCODE_MAX_LENGTH) ) {
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
                CHANGE_STATE(the_state, L, EJECT);
            }
            break;

        case WAIT_FOR_DECISION:
            if ( cast_or_spoil_timeout_expired() ) {
                spoil_button_light_off();
                cast_button_light_off();
                CHANGE_STATE(the_state, L, EJECT);
            } else if ( is_cast_button_pressed() ) {
                CHANGE_STATE(the_state, L, CAST);
            } else if ( is_spoil_button_pressed() ) {
                CHANGE_STATE(the_state, L, SPOIL);
            }
            break;

        case CAST:
            display_this_text(casting_ballot_text,
                              strlen(casting_ballot_text));
            cast_ballot();
            CHANGE_STATE(the_state, L, STANDBY);
            break;

        case SPOIL:
            spoil_ballot();
            CHANGE_STATE(the_state, L, AWAIT_REMOVAL);
            break;

        case EJECT:
            eject_ballot();
            CHANGE_STATE(the_state, L, AWAIT_REMOVAL);
            break;

        case AWAIT_REMOVAL:
            display_this_text(remove_ballot_text, strlen(remove_ballot_text));
            if ( !ballot_detected() ) {
                CHANGE_STATE(the_state, L, STANDBY);
            }
            break;

        case ABORT:
            break;

            //default:
            //assert(false);
        }

        update_sensor_state();
    }
}
