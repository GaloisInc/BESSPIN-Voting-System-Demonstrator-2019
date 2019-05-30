#include "static.h"
 void set_state(char* val) {
  the_state = val;
 //@ ghost gState = the_state;
 }
