/**
 * Smart Ballot Box Concrete Invariants & Refinement
 * @refine sbb.lando
 */
#ifndef __SBB_CONCR_INV_H_
#define __SBB_CONCR_INV_H_

#include "sbb_t.h"
#include "sbb.acsl"
#include "sbb_asm_prop.h"

#define SBB_Machine_Invariant(S, gpio_mem)      \
    (SBB_Invariant(S, gpio_mem) &&              \
     SBB_States_Invariant(S))

/*@ axiomatic SBB {
  @
  @   predicate SBB_String(char *s) =
  @     0 < strlen(s) && strlen(s) <= 255 && valid_read_string(s);
  @
  @   predicate SBB_Strings_Invariant =
  @     SBB_String(welcome_text) &&
  @     SBB_String(insert_ballot_text) &&
  @     SBB_String(barcode_detected_text) &&
  @     SBB_String(cast_or_spoil_line_1_text) &&
  @     SBB_String(cast_or_spoil_line_2_text) &&
  @     SBB_String(casting_ballot_text) &&
  @     SBB_String(spoiling_ballot_text) &&
  @     SBB_String(invalid_barcode_text) &&
  @     SBB_String(no_barcode_text) &&
  @     SBB_String(remove_ballot_text) &&
  @     SBB_String(error_line_1_text) &&
  @     SBB_String(error_line_2_text) &&
  @     SBB_String(sensor_in_pressed_msg) &&
  @     SBB_String(sensor_in_released_msg) &&
  @     SBB_String(sensor_out_pressed_msg) &&
  @     SBB_String(sensor_out_released_msg) &&
  @     SBB_String(cast_button_pressed_msg) &&
  @     SBB_String(cast_button_released_msg) &&
  @     SBB_String(spoil_button_pressed_msg) &&
  @     SBB_String(spoil_button_released_msg) &&
  @     SBB_String(barcode_scanned_msg) &&
  @     SBB_String(barcode_received_event_msg) &&
  @     SBB_String(empty_barcode_received_event_msg) &&
  @     SBB_String(invalid_barcode_received_event_msg) &&
  @     SBB_String(decision_timeout_event_msg) &&
  @     SBB_String(duplicate_barcode_line_1_text) &&
  @     SBB_String(duplicate_barcode_line_2_text) &&
  @     SBB_String(expired_ballot_line_1_text) &&
  @     SBB_String(expired_ballot_line_2_text) &&
  @     SBB_String(expired_ballot_received_event_msg) &&
  @     SBB_String(system_log_file_name) &&
  @     SBB_String(app_log_file_name);
  @
  @   predicate gpio_mem_button_lights(SBB_state S, uint8_t gpio_mem[8]) =
  @     (gpio_mem[BUTTON_CAST_LED] == 1  <==> cast_button_lit(S)) &&
  @     (gpio_mem[BUTTON_SPOIL_LED] == 1 <==> spoil_button_lit(S));
  @
  @   predicate gpio_mem_motors(SBB_state S, uint8_t gpio_mem[8]) =
  @     ((gpio_mem[MOTOR_0] == 0 && gpio_mem[MOTOR_1] == 1) <==>
  @        (S.M == MOTORS_TURNING_FORWARD)) &&
  @     ((gpio_mem[MOTOR_0] == 1 && gpio_mem[MOTOR_1] == 0) <==>
  @        (S.M == MOTORS_TURNING_BACKWARD)) &&
  @     ((gpio_mem[MOTOR_0] == 0 && gpio_mem[MOTOR_1] == 0) <==>
  @        (S.M == MOTORS_OFF));
  @
  @   predicate barcode_state(SBB_state S) =
  @     (0 <= barcode_length && barcode_length <= BARCODE_MAX_LENGTH) &&
  @     (S.L \in \union(CAST, SPOIL, WAIT_FOR_DECISION) ==>
  @       Barcode_Valid(&barcode[0], barcode_length)) &&
  @     (Barcode_Present(S) ==> barcode_length > 0);
  @
  @   predicate SBB_Invariant(SBB_state S, uint8_t gpio_mem[8]) =
  @     Log_IO_Initialized    &&
  @     gpio_mem_button_lights(S, gpio_mem) &&
  @     gpio_mem_motors(S, gpio_mem) &&
  @     barcode_state(S) &&
  @     Valid_ASM_States(the_state);
  @
  @  // predicate SBB_Machine_Invariant(SBB_state S, uint8_t gpio_mem[8]) =
  @  //   SBB_Invariant(S, gpio_mem) &&
  @  //   SBB_States_Invariant(S);
  @ }
  @
  @ axiomatic SBB_Concrete_Refinement {
  @
  @   // Button light refinements
  @   predicate cbl_gpio_rel(cast_button_light cbl, uint8_t i) =
  @     (i == 1)  <==> (cbl == lit);
  @   predicate sbl_gpio_rel(spoil_button_light sbl, uint8_t i) =
  @     (i == 1) <==> (sbl == lit);
  @
  @   // Barcode refinement
  @   predicate barcode_rel(has_barcode hw_barcode, barcode_t barcode, barcode_length_t len) =
  @     Barcode_Valid(barcode, len) <==> (hw_barcode == has_valid_barcode);
  @
  @   // Motor refinement
  @   predicate motor_gpio_rel(motor m, uint8_t f, uint8_t b) =
  @     ((b == 0 && f == 1) <==> m == forward)  &&
  @     ((b == 1 && f == 0) <==> m == backward) &&
  @     ((b == 0 && f == 0) <==> m == off);
  @
  @   // We can really only model when the machine *thinks*
  @   // paper is present. Moreover, even if the sensor is not active,
  @   // paper may still be present (if we've fed it in) hence:
  @   predicate paper_present_rel(paper_present p, SBB_state S) =
  @     (p == present) <==> Paper_Present(S);
  @
  @   // The refinement relation
  @   predicate SBB_Refinement(// Logical HW state
  @                              has_barcode hw_barcode,
  @                              cast_button cb,
  @                              spoil_button sb,
  @                              paper_feed_motor m,
  @                              paper_present p,
  @                              cast_button_light cbl,
  @                              spoil_button_light sbl,
  @                              // Concrete State
  @                              SBB_state S,
  @                              barcode_t barcode,
  @                              barcode_length_t len,
  @                              uint8_t io[8]) =
  @       paper_present_rel(p, S) &&
  @       motor_gpio_rel(m, io[MOTOR_1], io[MOTOR_0]) &&
  @       barcode_rel(hw_barcode, barcode, len)  &&
  @       cbl_gpio_rel(cbl, io[BUTTON_CAST_LED]) &&
  @       sbl_gpio_rel(sbl, io[BUTTON_SPOIL_LED]);
  @
  @   // Helpers:
  @  // lemma sbb_concr_lights_jointness:
  @  //   \forall has_barcode hw_barcode,
  @  //           cast_button cb,
  @  //           spoil_button sb,
  @  //           paper_feed_motor m,
  @  //           paper_present p,
  @  //           cast_button_light cbl,
  @  //           spoil_button_light sbl,
  @  //           SBB_state S;
  @  //     SBB_Refinement(hw_barcode, cb, sb, m, p, cbl, sbl,
  @  //                    S, &barcode[0], barcode_length, gpio_mem) &&
  @  //     SBB_Machine_Invariant(S, gpio_mem) &&
  @  //     S.L != ABORT
  @  //  // -----------------------------------------------------------
  @  //   ==> (cast_button_lit(S) <==> spoil_button_lit(S));
  @
  @   // Main lemmas.
  @   // Each conclusion should be a property from sbb.acsl
  @   lemma SBB_Impl_Prop_Lights_Jointness:
  @     \forall has_barcode hw_barcode,
  @             cast_button cb,
  @             spoil_button sb,
  @             paper_feed_motor m,
  @             paper_present p,
  @             cast_button_light cbl,
  @             spoil_button_light sbl,
  @             SBB_state S;
  @       SBB_Refinement(hw_barcode, cb, sb, m, p, cbl, sbl,
  @                      S, &barcode[0], barcode_length, gpio_mem) &&
  @       SBB_Machine_Invariant(S, gpio_mem) &&
  @       S.L != ABORT
  @    // -----------------------------------------------------------
  @     ==> Prop_Lights_On_Jointness(cbl, sbl);
  @
  @   lemma SBB_Impl_Prop_Only_Valid_Barcode:
  @     \forall has_barcode hw_barcode,
  @             cast_button cb,
  @             spoil_button sb,
  @             paper_feed_motor m,
  @             paper_present p,
  @             cast_button_light cbl,
  @             spoil_button_light sbl,
  @             SBB_state S;
  @       SBB_Refinement(hw_barcode, cb, sb, m, p, cbl, sbl,
  @                      S, &barcode[0], barcode_length, gpio_mem) &&
  @       SBB_Machine_Invariant(S, gpio_mem) &&
  @       S.L != ABORT
  @    // -----------------------------------------------------------
  @     ==> Prop_Only_Valid_Barcode(S, hw_barcode);
  @
  @   lemma SBB_Impl_Prop_Lights_On_With_Ballot:
  @     \forall has_barcode hw_barcode,
  @             cast_button cb,
  @             spoil_button sb,
  @             paper_feed_motor m,
  @             paper_present p,
  @             cast_button_light cbl,
  @             spoil_button_light sbl,
  @             SBB_state S;
  @       SBB_Refinement(hw_barcode, cb, sb, m, p, cbl, sbl,
  @                      S, &barcode[0], barcode_length, gpio_mem) &&
  @       SBB_Machine_Invariant(S, gpio_mem) &&
  @       S.L != ABORT
  @    // -----------------------------------------------------------
  @     ==> Prop_Lights_On_WithBallot(hw_barcode, cbl, sbl);
  @
  @   lemma SBB_Impl_Prop_Lights_Off_Power_On:
  @     \forall has_barcode hw_barcode,
  @             cast_button cb,
  @             spoil_button sb,
  @             paper_feed_motor m,
  @             paper_present p,
  @             cast_button_light cbl,
  @             spoil_button_light sbl,
  @             SBB_state S;
  @       SBB_Refinement(hw_barcode, cb, sb, m, p, cbl, sbl,
  @                      S, &barcode[0], barcode_length, gpio_mem) &&
  @       SBB_Machine_Invariant(S, gpio_mem) &&
  @       S.L != ABORT
  @    // -----------------------------------------------------------
  @     ==> Prop_Lights_Off_Power_On(S, cbl, sbl);
  @
  @   lemma SBB_Impl_Prop_Initialized_Motor_Off:
  @     \forall has_barcode hw_barcode,
  @             cast_button cb,
  @             spoil_button sb,
  @             paper_feed_motor m,
  @             paper_present p,
  @             cast_button_light cbl,
  @             spoil_button_light sbl,
  @             SBB_state S;
  @       SBB_Refinement(hw_barcode, cb, sb, m, p, cbl, sbl,
  @                      S, &barcode[0], barcode_length, gpio_mem) &&
  @       SBB_Machine_Invariant(S, gpio_mem) &&
  @       S.L != ABORT
  @    // -----------------------------------------------------------
  @     ==> Prop_Initialized_Motor_Off(S, m);
  @
  @   lemma SBB_Impl_Prop_Motor_On_Paper_Present:
  @     \forall has_barcode hw_barcode,
  @             cast_button cb,
  @             spoil_button sb,
  @             paper_feed_motor m,
  @             paper_present p,
  @             cast_button_light cbl,
  @             spoil_button_light sbl,
  @             SBB_state S;
  @       SBB_Refinement(hw_barcode, cb, sb, m, p, cbl, sbl,
  @                      S, &barcode[0], barcode_length, gpio_mem) &&
  @       SBB_Machine_Invariant(S, gpio_mem) &&
  @       S.L != ABORT
  @    // -----------------------------------------------------------
  @     ==> Prop_Motor_On_Paper_Present(p, m);
  @ }
*/

// This is temporary, to get around frama-c issues
// with strings. This is sound as long as:
// 1. none of our constant strings alias,
// 2. all of the strings actually satisfy SBB_String
/*@ assigns \nothing;
  @ ensures SBB_Strings_Invariant;
*/
void __assume_strings_OK(void);

/*@ axiomatic STRINGS_AXIOM {
  @    axiom strings_ok: SBB_Strings_Invariant;
  @ }
*/
#endif
