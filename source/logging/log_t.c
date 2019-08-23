#include "logging/log_t.h"

void copy_log_entry (log_entry dst,       // OUT
		     const log_entry src) // IN
{
  /*@
    loop invariant 0 <= j <= LOG_ENTRY_LENGTH;
    loop invariant \forall integer k; 0 <= k < j ==> dst[k] == src[k];
    loop assigns j, dst[0 .. LOG_ENTRY_LENGTH - 1];
    loop variant LOG_ENTRY_LENGTH - j;
  */
  for (int j = 0; j < LOG_ENTRY_LENGTH; j++)
    {
      dst[j] = src[j];
    }

}
