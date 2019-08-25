#include "sbb.h"
#include "sbb_globals.h"
#include "sbb_invariants.h"

/*@ requires SBB_Invariant(the_state, gpio_mem);
  @ ensures \false;
*/
void sbb_invariant_smoketest(void) {}

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ ensures \false;
@*/
void sbb_machine_invariant_smoketest(void) {}
