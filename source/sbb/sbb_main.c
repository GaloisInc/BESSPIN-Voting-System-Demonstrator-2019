#include "sbb.h"
#include <stdio.h>
#include <string.h>

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

void ballot_box_main_loop(void)
{
    char this_barcode[BARCODE_MAX_LENGTH] = {0};
    // Init happens before calling main()
    for (;;)
    {
        go_to_standby();
        if (ballot_detected())
        {
            ballot_detect_timeout_reset();
            while (!ballot_inserted() && !ballot_detect_timeout_expired())
            {
                move_motor_forward();
            }
            stop_motor();

            if (has_a_barcode())
            {
                display_this_text(barcode_detected_text,
                                  strlen(barcode_detected_text));
                what_is_the_barcode(this_barcode, BARCODE_MAX_LENGTH);

                if (is_barcode_valid(this_barcode, BARCODE_MAX_LENGTH))
                {
                    display_this_text(cast_or_spoil_text,
                                      strlen(cast_or_spoil_text));
                    cast_button_light_on();
                    spoil_button_light_on();
                    cast_or_spoil_timeout_reset();

                    while (!cast_or_spoil_timeout_expired() &&
                           !is_cast_button_pressed() &&
                           !is_spoil_button_pressed())
                    {
                        ;
                        ;
                    }
                    if (is_cast_button_pressed())
                    {
                        spoil_button_light_off();
                        display_this_text(casting_ballot_text,
                                          strlen(casting_ballot_text));
                        cast_ballot();
                        cast_button_light_off();
                        continue; // directly to Standby
                    }
                    else
                    {
                        cast_button_light_off();
                        spoil_button_light_off();
                        // ->  spoil ballot
                    }
                }
                else
                {
                    display_this_text(not_a_valid_barcode_text,
                                      strlen(not_a_valid_barcode_text));
                    // ->  spoil ballot
                }
            }
            else
            { // if has_a_barcode
                display_this_text(no_barcode_text, strlen(no_barcode_text));
                // -> spoil ballot
            }
            display_this_text(spoiling_ballot_text,
                              strlen(spoiling_ballot_text));
            spoil_ballot();
            display_this_text(remove_ballot_text, strlen(remove_ballot_text));
            while (!ballot_spoiled())
            {
                ;
                ;
            }
        } // if ballot_detected
    }     // loop iteration
}
