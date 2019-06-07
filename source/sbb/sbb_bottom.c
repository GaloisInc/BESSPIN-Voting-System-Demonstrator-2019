/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

/**
 * Initialize peripherals
 */
void init_sbb(void) {
    ;;
}

/**
 * Perform Tally!
 */
void perform_tally(void)
{
    printf("Performing tally\r\n");
}

/**
 * Is barcode valid?
 * Check validity of the given barcode string
 */
bool is_barcode_valid(char * str, uint8_t len)
{
    assert(false);
    //@ assert false;
    return false;
}

/**
 * Is Cast button pressed?
 */
bool is_cast_button_pressed(void) {
    assert(false);
    //@ assert false;
    return false;
}

/**
 * Is Spoil button pressed?
 */
bool is_spoil_button_pressed(void) {
    assert(false);
    //@ assert false;
    return false;
}

/**
 * Just received barcode!
 */
void just_received_barcode(void) {
    assert(false);
    //@ assert false;
}

/**
 * Set barcode to this value
 */
void set_received_barcode(char *str, uint8_t len) {
    assert(false);
    //@ assert false;
}


/**
 * Has a barcode?
 */
bool has_a_barcode(void) {
    assert(false);
    //@ assert false;
    return false;
}

/**
 * What is the barcode?
 */
void what_is_the_barcode(char *str, uint8_t len) {
    assert(false);
    //@ assert false;
}

/**
 * Spoil Button Light On!
 */
void spoil_button_light_on(void) {
    assert(false);
    //@ assert false;
}

/**
 * Spoil Button Light Off!
 */
void spoil_button_light_off(void) {
    assert(false);
    //@ assert false;
}

/**
 * Cast Button Light On!
 */
void cast_button_light_on(void) {
    assert(false);
    //@ assert false;
}

/**
 * Cast Button Light Off!
 */
void cast_button_light_off(void) {
    assert(false);
    //@ assert false;
}

/**
 * Move Motor Forward!
 */
void move_motor_forward(void) {
    assert(false);
    //@ assert false;
}

/**
 * Move Motor back!
 */
void move_motor_back(void) {
    assert(false);
    //@ assert false;
}

/**
 * Stop Motor!
 */
void stop_motor(void) {
    assert(false);
    //@ assert false;
}

/**
 * Display this text!
 */
void display_this_text(char *str, uint8_t len) {
    assert(false);
    //@ assert false;
}

/**
 * Ballot detected?
 */
bool ballot_detected(void) {
    assert(false);
    //@ assert false;
    return false;
}

/**
 * Ballot inserted?
 */
bool ballot_inserted(void) {
    assert(false);
    //@ assert false;
    return false;
}

/**
 * Spoil ballot!
 */
void spoil_ballot(void) {
    assert(false);
    //@ assert false;
}
  
/**
 * Cast ballot!
 */
void cast_ballot(void) {
    assert(false);
    //@ assert false;
}

/**
 * Ballot spoiled?
 */
bool ballot_spoiled(void) {
    assert(false);
    //@ assert false;
    return false;
}

/**
 * Go to standby!
 */
void go_to_standby(void) {
    assert(false);
    //@ assert false;
}

/**
 * Ballot Detect Timeout Reset!
 */
void ballot_detect_timeout_reset(void) {
    assert(false);
    //@ assert false;
}

/**
 * Ballot Detect Timeout Expired?
 */
bool ballot_detect_timeout_expired(void) {
    assert(false);
    //@ assert false;
    return false;
}

/**
 * Cast Or Spoil Timeout Reset!
 */
void cast_or_spoil_timeout_reset(void) {
    assert(false);
    //@ assert false;
}

/**
 * Cast Or Spoil Timeout Expired?
 */
bool cast_or_spoil_timeout_expired(void) {
    assert(false);
    //@ assert false;
    return false;
}


int main(void) {
    printf("starting");
    ballot_box_main_loop();
}
