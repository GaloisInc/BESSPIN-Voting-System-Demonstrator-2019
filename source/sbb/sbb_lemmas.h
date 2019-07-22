#include "sbb_t.h"
#include "sbb.h"

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L != ABORT;
  @ ensures cast_button_lit(the_state) <==> spoil_button_lit(the_state);
*/
void lemma_button_lights_jointness(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L != ABORT;
  @ ensures cast_button_lit(the_state) ==> Ballot_Present(the_state);
  @ ensures spoil_button_lit(the_state) ==> Ballot_Present(the_state);
*/
void lemma_button_lights_ballot(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L != ABORT;
  @ ensures the_state.L == INITIALIZE ==> !cast_button_lit(the_state);
  @ ensures the_state.L == INITIALIZE ==> !spoil_button_lit(the_state);
*/
void lemma_button_lights_power_on_dark(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L != ABORT;
  @ ensures the_state.L == INITIALIZE ==> the_state.M == MOTORS_OFF;
*/
void lemma_motor_initial_state(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L != ABORT;
  @ ensures the_state.M != MOTORS_OFF ==> Paper_Present(the_state);
@*/
void lemma_motor_paper_present(void);

/* requires SBB_Machine_Invariant;
   requries PaperDetected(s1);
   requires T(s1, s2);
   ensures s2.L == EJECT;
*/
void lemma_paper_ejected_power_on(SBB_state s1, SBB_state s2);
