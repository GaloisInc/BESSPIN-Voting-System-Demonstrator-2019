/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"
#include "sbb_freertos.h"
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes */
#include <FreeRTOS.h>
#include <task.h>
#include <stddef.h>

#include "gpio.h"
#include "serLcd.h"

/* Motor defines */
#define MOTOR_0 4
#define MOTOR_1 5

/* Timeouts */
#define BALLOT_DETECT_TIMEOUT_MS 6000
#define CAST_OR_SPOIL_TIMEOUT_MS 30000

// Text defines
const char *insert_ballot_text = "Insert ballot.";
const char *barcode_detected_text = "Barcode detected.";
const char *cast_or_spoil_text = "Spoil or Cast?";
const char *casting_ballot_text = "Casting ballot...";
const char *spoiling_ballot_text = "Spoiling ballot...";
const char *not_a_valid_barcode_text = "Invalid barcode!";
const char *no_barcode_text = "No barcode!";
const char *remove_ballot_text = "Remove ballot!";
const char *something_weird_text = "Eek! Alert dmz!";
const char *scanning_ballot_text = "Scanning ballot...";

/**
 * Initialize peripherals
 */
void init_sbb(void)
{
    gpio_set_as_output(MOTOR_0);
    gpio_set_as_output(MOTOR_1);
    gpio_set_as_output(BUTTON_CAST_LED);
    gpio_set_as_output(BUTTON_SPOIL_LED);
}

/**
 * Perform Tally!
 */
void perform_tally(void) { printf("Performing tally\r\n"); }

/**
 * Is barcode valid?
 * Check validity of the given barcode string
 */
bool is_barcode_valid(char *str, uint8_t len)
{
    (void)str;
    (void)len;
    return true;
}

/**
 * Is Cast button pressed?
 */
bool is_cast_button_pressed(void) { return gpio_read(BUTTON_CAST_IN); }

/**
 * Is Spoil button pressed?
 */
bool is_spoil_button_pressed(void) { return gpio_read(BUTTON_SPOIL_IN); }

/**
 * Just received barcode!
 */
void just_received_barcode(void)
{
    ;;
}

/**
 * Set barcode to this value
 */
void set_received_barcode(char *str, uint8_t len)
{
    ;;
}

/**
 * Has a barcode?
 */
bool has_a_barcode(void)
{
    return false;
}

/**
 * What is the barcode?
 */
void what_is_the_barcode(char *str, uint8_t len)
{
    ;;
}

/**
 * Spoil Button Light On!
 */
void spoil_button_light_on(void) { gpio_write(BUTTON_SPOIL_LED); }

/**
 * Spoil Button Light Off!
 */
void spoil_button_light_off(void) { gpio_clear(BUTTON_SPOIL_LED); }

/**
 * Cast Button Light On!
 */
void cast_button_light_on(void) { gpio_write(BUTTON_CAST_LED); }

/**
 * Cast Button Light Off!
 */
void cast_button_light_off(void) { gpio_clear(BUTTON_CAST_LED); }

/**
 * Move Motor Forward!
 */
void move_motor_forward(void)
{
    gpio_clear(MOTOR_0);
    gpio_write(MOTOR_1);
}

/**
 * Move Motor back!
 */
void move_motor_back(void)
{
    gpio_write(MOTOR_0);
    gpio_clear(MOTOR_1);
}

/**
 * Stop Motor!
 */
void stop_motor(void)
{
    gpio_clear(MOTOR_0);
    gpio_clear(MOTOR_1);
}

/**
 * Display this text!
 */
void display_this_text(const char *str, uint8_t len) { serLcdPrintf(str, len); }

/**
 * Ballot detected?
 */
bool ballot_detected(void) { return !gpio_read(PAPER_SENSOR_IN); }

/**
 * Ballot inserted?
 */
bool ballot_inserted(void) { return !gpio_read(PAPER_SENSOR_OUT); }

/**
 * Spoil ballot!
 */
void spoil_ballot(void)
{
    cast_button_light_off();
    spoil_button_light_off();
    move_motor_back();
    for(;;) {
        if (!ballot_inserted() && ballot_detected()) {
            printf("Ready to remove paper\r\n");
            break;
        }
    }
    stop_motor();
}

/**
 * Cast ballot!
 */
void cast_ballot(void)
{
    cast_button_light_off();
    spoil_button_light_off();
    move_motor_forward();
    for(;;) {
        if (!ballot_inserted()) {
            printf("Casted?\r\n");
            break;
        }
    }
    stop_motor();
}

/**
 * Ballot spoiled?
 */
bool ballot_spoiled(void) { return (!ballot_detected() && !ballot_inserted()); }

/**
 * Go to standby!
 */
void go_to_standby(void)
{
    stop_motor();
    cast_button_light_off();
    spoil_button_light_off();
    display_this_text(insert_ballot_text, strlen(insert_ballot_text));
}

/**
 * Ballot Detect Timeout Reset!
 */
void ballot_detect_timeout_reset(void)
{
    ;
}

/**
 * Ballot Detect Timeout Expired?
 */
bool ballot_detect_timeout_expired(void)
{
    return false;
}

/**
 * Cast Or Spoil Timeout Reset!
 */
void cast_or_spoil_timeout_reset(void)
{
    ;;
}

/**
 * Cast Or Spoil Timeout Expired?
 */
bool cast_or_spoil_timeout_expired(void)
{
    return false;
}

void ballot_box_main_loop(void)
{
    char barcode[BARCODE_MAX_LENGTH] = {0};
    size_t xReceiveLength = 0;
	bool normal_feed = false;
	    
    EventBits_t uxReturned;

    printf("starting");
    init_sbb();

    for (;;)
    {
        go_to_standby();

        printf("Waiting for a ballot\r\n");
        uxReturned = xEventGroupWaitBits(xSBBEventGroup,
                                         ebPAPER_SENSOR_IN_PRESSED, pdTRUE,
                                         pdFALSE, portMAX_DELAY);

        printf("uxReturned = 0x%lx\r\n",uxReturned);
        if (uxReturned & ebPAPER_SENSOR_IN_PRESSED) {
            printf("Ballot detected: ebPAPER_SENSOR_IN_PRESSED\r\n");
        } else {
            ;;
        }

        display_this_text(scanning_ballot_text, strlen(scanning_ballot_text));
        move_motor_forward();

        printf("Waiting for ebPAPER_SENSOR_IN_RELEASED\r\n");

        uxReturned =
            xEventGroupWaitBits(xSBBEventGroup, ebPAPER_SENSOR_IN_RELEASED,
                                pdTRUE, pdFALSE, pdMS_TO_TICKS(10000));

		
        if (uxReturned & ebPAPER_SENSOR_IN_RELEASED)
        {
            printf("ebPAPER_SENSOR_IN_RELEASED in time\r\n");
 
 			normal_feed = true;
	        printf("Stop motor\r\n");
    	    stop_motor();
           // TODO: do we have a barcode?
            uxReturned =
            xEventGroupWaitBits(xSBBEventGroup, ebBARCODE_SCANNED,
                                pdTRUE, pdFALSE, pdMS_TO_TICKS(100));
            if (uxReturned & ebBARCODE_SCANNED) {
                printf("We got ebBARCODE_SCANNED\r\n");
                printf("Barcode received\r\n");
            } else {
                printf("No ebBARCODE_SCANNED\r\n");
                display_this_text(no_barcode_text, strlen(no_barcode_text));
            }
        }
        else
        {
            printf("ebPAPER_SENSOR_IN_RELEASED timeout\r\n");
            display_this_text(no_barcode_text, strlen(no_barcode_text));
            move_motor_forward();
            vTaskDelay(5000);
            stop_motor();
        }


        // /* See if we got a barcode */
        xReceiveLength = xStreamBufferReceive(xScannerStreamBuffer,
                                           (void *)barcode, sizeof(barcode),
                                           SCANNER_BUFFER_RX_BLOCK_TIME_MS);

        if (normal_feed && xReceiveLength > 0)
        {
            display_this_text(cast_or_spoil_text, strlen(cast_or_spoil_text));
            cast_button_light_on();
            spoil_button_light_on();

            xEventGroupClearBits( xSBBEventGroup, ebCAST_BUTTON_PRESSED | ebSPOIL_BUTTON_PRESSED );
            uxReturned =
            xEventGroupWaitBits(xSBBEventGroup, ebCAST_BUTTON_PRESSED | ebSPOIL_BUTTON_PRESSED,
                                pdTRUE, pdFALSE, pdMS_TO_TICKS(60000));
            if (uxReturned & ebCAST_BUTTON_PRESSED) {
                printf("We got ebCAST_BUTTON_PRESSED\r\n");

                // cast
                display_this_text(casting_ballot_text, strlen(casting_ballot_text));
                move_motor_forward();
            	cast_button_light_off();
            	spoil_button_light_off();

                vTaskDelay(5000);
                stop_motor();

                printf("Done!\r\n");
                continue;
            } else if (uxReturned & ebSPOIL_BUTTON_PRESSED) {
                printf("We got ebSPOIL_BUTTON_PRESSED\r\n");
                
                // spoil - but really cast anyway since no reverse motor
                display_this_text(spoiling_ballot_text, strlen(spoiling_ballot_text));
                move_motor_forward();
                cast_button_light_off();
	            spoil_button_light_off();

                vTaskDelay(5000);
                stop_motor();
            } else {
                printf("Something else happened\r\n");
                
                display_this_text(something_weird_text, strlen(something_weird_text));
                move_motor_forward();
                
                vTaskDelay(5000);
                stop_motor();
            }
        }
        else if (normal_feed)
        {
            printf("Barcode RX timeout\r\n");
            display_this_text(no_barcode_text, strlen(no_barcode_text));
            move_motor_forward();
            vTaskDelay(5000);
            stop_motor();
        }
    } // loop iteration
}
