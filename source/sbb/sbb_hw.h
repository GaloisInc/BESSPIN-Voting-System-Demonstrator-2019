/**
 * Smart Ballot Box HW Abstraction API
 * @refine sbb.lando
 */
#include <stdbool.h>
#include "sbb_t.h"

/*@ requires \valid(year);
  @ requires \valid(month);
  @ requires \valid(day);
  @ requires \valid(hour);
  @ requires \valid(minute);
  @ requires \separated(month, day);
  @ requires \separated(month, hour);
  @ requires \separated(month, minute);
  @ requires \separated(day, hour);
  @ requires \separated(day, minute);
  @ requires \separated(hour, minute);
  @ assigns *year, *month, *day, *hour, *minute;
  @ ensures \result == true || \result == false;
*/
bool hw_get_current_time(uint32_t *year, uint16_t *month, uint16_t *day,
                         uint16_t *hour, uint16_t *minute);
