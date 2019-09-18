#ifndef __LOG_NET_H__
#define __LOG_NET_H__

#include "log_net_t.h"
#include "secure_log_t.h"

// Abstract ghost state representing the overall state
// of the reporting system

//@ ghost int reporting_system;

/*@
  axiomatic log_net_axioms {

  predicate
    Log_Net_Initialized{L} reads reporting_system; // abstract
  }
*/


/*@ assigns reporting_system \from \nothing;
    ensures Log_Net_Initialized;
 */
void osd_Log_Net_Initialize(void);

/*@ requires \valid_read(Transmit_Buffer + (0 .. total - 1));
    assigns  reporting_system \from reporting_system, Transmit_Buffer, total;
*/
void Log_Net_Send(const char *remote_file_name, uint8_t *Transmit_Buffer, size_t total);

/*@ requires \valid_read(Transmit_Buffer + (0 .. total - 1));
    assigns  reporting_system \from reporting_system, Transmit_Buffer, total;
*/
void osd_Log_Net_Send(uint8_t *Transmit_Buffer, size_t total);

#endif /* __LOG_NET_H__ */
