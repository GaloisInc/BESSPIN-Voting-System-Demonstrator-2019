#define INITSTATE "gaga"
 //@ ghost char* gState=INITSTATE;
static char* the_state = 0;
 /*@ axiomatic State { 
   logic char* abstract_region;  
   axiom internal_state: abstract_region == the_state;
}
@*/

/*@
  @  assigns gState, *abstract_region, the_state;
  @  ensures val == gState;
  @*/
 void set_state(char* val);
