/**
 * Smart Ballot Box API
 * based on sbb.lando
 */

#include "sbb_hw.h"
#include <string.h>
#include <stdio.h>

/**
 * component Ballot Box
 * Deposit ballot!
 */
void deposit_ballot(void)
{
    printf("Ballot deposited!");
}


/**
 * component Barcode Scanner
 * Has a valid barcode?
 */
bool has_a_valid_bardcode(struct BarcodeScanner * sensor)
{
    return sensor->has_barcode;
}

/**
 * component Barcode Scanner
 * What is the barcode?
 */
void what_is_the_barcode(struct BarcodeScanner * sensor, char *str, uint8_t len)
{
    // TODO: this has to be mutex protected
    // memcpy(str, sensor->barcode, (len > BARCODE_MAX_LENGTH) ? BARCODE_MAX_LENGTH : len);
    // sensor->has_barcode = false;
}

/**
 * component LEDButton
 * Is button pressed?
 */
bool is_button_pressed(struct LedButton *button)
{
    // TODO: proper GPIO
    return false;
}

/**
 * component LEDButton
 * Button Light On!
 */
void button_light_on(struct LedButton *button)
{
    // TODO: proper GPIO
    ;;
}

/**
 * component LEDButton
 * Button Light Off!
 */
void button_light_off(struct LedButton *button)
{
    // TODO: proper GPIO
    ;;
}

/**
 * component Motor
 * Motor Forward!
 */
void motor_forward(void)
{
    // TODO: proper GPIO
    ;;
}

/**
 * component Motor
 * Motor Backward!
 */
void motor_backward(void)
{
    // TODO: proper GPIO
    ;;
}

/**
 * component Motor
 * Motor Stop!
 */
void motor_stop(void)
{
    // TODO: proper GPIO
    ;;
}

/**
 * component LCD Display
 * Display this text!
 */
void display_this_text(char *str, uint8_t len)
{
    (void) len;
    printf("%s\r\n", str);
}

/**
 * component Paper Sensor
 * Paper detected ?
 */
bool is_paper_detected(struct PaperSensor * sensor)
{
    (void)sensor;
    return false;
}
