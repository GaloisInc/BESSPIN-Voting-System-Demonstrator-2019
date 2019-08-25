/**
 * Smart Ballot Box high level properties
 * @refine sbb.lando
 */

#ifndef __SBB_ASM_PROPS__
#define __SBB_ASM_PROPS__

#include "sbb.acsl"
#include "sbb_t.h"
#include "sbb_logging.h"
#include "sbb_io_constants.h"

// Derived from sbb/requirements.lando:
/*@ axiomatic SBB_Properties {
  @
  @   predicate Accepted_Barcode(SBB_state S) =
  @     S.L \in \union(WAIT_FOR_DECISION, CAST, SPOIL);
  @
  @   predicate Prop_Only_Valid_Barcode(SBB_state S, has_barcode barcode) =
  @     Accepted_Barcode(S) ==> (barcode == has_valid_barcode);
  @
  @   predicate Prop_Lights_On_WithBallot(has_barcode barcode,
  @                                       cast_button_light cbl,
  @                                       spoil_button_light sbl) =
  @     (cbl == lit || sbl == lit) ==> (barcode == has_valid_barcode);
  @
  @   predicate Prop_Lights_On_Jointness(cast_button_light cbl, spoil_button_light sbl) =
  @     (cbl == lit) <==> (sbl == lit);
  @
  @   predicate Prop_Lights_Off_Power_On(SBB_state S,
  @                                      cast_button_light cbl,
  @                                      spoil_button_light sbl) =
  @     (S.L == STANDBY) ==> (cbl == dark && sbl == dark);
  @
  @   predicate Prop_Initialized_Motor_Off(SBB_state S, motor m) =
  @     S.L \in \union(INITIALIZE, STANDBY) ==> m == off;
  @
  @   predicate Prop_Motor_On_Paper_Present(paper_present p, motor m) =
  @     (m != off) ==> (p != none);
  @ }
  @
  @ axiomatic SBB_States_Invariants {
  @
  @   predicate valid_range(integer lo, integer x, integer hi) =
  @     lo <= x && x <= hi;
  @
  @   predicate M_ASM_valid(SBB_state S) =
  @     valid_range(MOTORS_OFF, S.M, MOTORS_TURNING_BACKWARD);
  @
  @   predicate L_ASM_valid(SBB_state S) =
  @     valid_range(INITIALIZE, S.L, ABORT);
  @
  @   predicate D_ASM_valid(SBB_state S) =
  @     valid_range(INITIALIZED_DISPLAY, S.D, SHOWING_TEXT);
  @
  @   predicate BS_ASM_valid(SBB_state S) =
  @     valid_range(BARCODE_NOT_PRESENT, S.BS, BARCODE_PRESENT_AND_RECORDED);
  @
  @   predicate P_ASM_valid(SBB_state S) =
  @     valid_range(NO_PAPER_DETECTED, S.P, PAPER_DETECTED);
  @
  @   predicate FS_ASM_valid(SBB_state S) =
  @     valid_range(LOG_OK, S.FS, LOG_FAILURE);
  @
  @   predicate Barcode_Present(SBB_state S) =
  @    S.BS == BARCODE_PRESENT_AND_RECORDED;
  @
  @   predicate Valid_ASM_States(SBB_state S) =
  @     M_ASM_valid(S) &&
  @     L_ASM_valid(S) &&
  @     D_ASM_valid(S) &&
  @     P_ASM_valid(S) &&
  @     FS_ASM_valid(S) &&
  @     BS_ASM_valid(S);
  @
  @   predicate Initialize_Inv(SBB_state S) =
  @     S.M == MOTORS_OFF   &&
  @     !cast_button_lit(S) &&
  @     !spoil_button_lit(S);
  @
  @   predicate Standby_Inv(SBB_state S) =
  @     S.M == MOTORS_OFF   &&
  @     !cast_button_lit(S) &&
  @     !spoil_button_lit(S);
  @
  @   predicate Wait_For_Ballot_Inv(SBB_state S) =
  @     S.M == MOTORS_OFF   &&
  @     !cast_button_lit(S) &&
  @     !spoil_button_lit(S);
  @
  @   predicate Feed_Ballot_Inv(SBB_state S) =
  @     !cast_button_lit(S)           &&
  @     !spoil_button_lit(S);
  @
  @   predicate Barcode_Detected_Inv(SBB_state S) =
  @     Barcode_Present(S)       &&
  @     !cast_button_lit(S)      &&
  @     !spoil_button_lit(S);
  @
  @   predicate Wait_For_Decision_Inv(SBB_state S) =
  @     Barcode_Present(S) &&
  @     cast_button_lit(S) &&
  @     spoil_button_lit(S);
  @
  @   axiom unfold_wait:
  @     \forall SBB_state S;
  @     Wait_For_Decision_Inv(S) <==>
  @       (Barcode_Present(S) &&
  @        cast_button_lit(S) &&
  @        spoil_button_lit(S));
  @
  @   predicate Cast_Inv(SBB_state S) =
  @     Barcode_Present(S) &&
  @     !cast_button_lit(S) &&
  @     !spoil_button_lit(S);
  @
  @   predicate Spoil_Inv(SBB_state S) =
  @     Barcode_Present(S) &&
  @     !cast_button_lit(S) &&
  @     !spoil_button_lit(S);
  @
  @   predicate Eject_Inv(SBB_state S) =
  @     !cast_button_lit(S)  &&
  @     !spoil_button_lit(S);
  @
  @   predicate Await_Removal_Inv(SBB_state S) =
  @     S.M == MOTORS_OFF     &&
  @     !cast_button_lit(S)   &&
  @     !spoil_button_lit(S);
  @
  @   predicate Abort_Inv(SBB_state S) =
  @     true;
  @
  @   predicate Ballot_Present(SBB_state S) =
  @      S.L == BARCODE_DETECTED  ||
  @      S.L == WAIT_FOR_DECISION ||
  @      S.L == CAST              ||
  @      S.L == EJECT             ||
  @      S.L == SPOIL;
  @
  @   predicate Paper_Present(SBB_state S) =
  @     S.P == PAPER_DETECTED ||
  @     Ballot_Present(S)     ||
  @     S.L == FEED_BALLOT    ||
  @     S.L == AWAIT_REMOVAL;
  @
  @   // Since we only have one sensor, we consider paper to be present
  @   // in some cases beyond the sensor being active
  @   // (like if we have fed it far enough that the sensor is no longer active)
  @   // Moreover, since we are polling, this definition is when we _think_ there
  @   // is paper present (we don't allow the sensor to pre-empt the executing SBB task)
  @
  @   predicate SBB_States_Invariant(SBB_state S) =
  @      (S.L == WAIT_FOR_BALLOT   && Wait_For_Ballot_Inv(S))   ||
  @      (S.L == FEED_BALLOT       && Feed_Ballot_Inv(S))       ||
  @      (S.L == BARCODE_DETECTED  && Barcode_Detected_Inv(S))  ||
  @      (S.L == WAIT_FOR_DECISION && Wait_For_Decision_Inv(S)) ||
  @      (S.L == CAST              && Cast_Inv(S))              ||
  @      (S.L == SPOIL             && Spoil_Inv(S))             ||
  @      (S.L == EJECT             && Eject_Inv(S))             ||
  @      (S.L == AWAIT_REMOVAL     && Await_Removal_Inv(S))     ||
  @      (S.L == ABORT             && Abort_Inv(S))             ||
  @      (S.L == STANDBY           && Standby_Inv(S))           ||
  @      (S.L == INITIALIZE        && Initialize_Inv(S));
  @ }
*/

#endif
