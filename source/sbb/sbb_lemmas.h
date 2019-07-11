#include "sbb_t.h"
#include "sbb.h"

/*@ requires SBB_Machine_Invariant;
  @ ensures cast_button_lit(the_state) <==> spoil_button_lit(the_state);
*/
void lemma_button_lights_disjoint(void);
