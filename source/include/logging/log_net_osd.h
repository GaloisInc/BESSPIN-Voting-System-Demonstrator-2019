#ifndef __LOG_NET_OSD_H__
#define __LOG_NET_OSD_H__

#include "log_net_t.h"
#include "secure_log_t.h"
#include "log_net.h"

/*@ assigns reporting_system \from \nothing;
  ensures Log_Net_Initialized;
*/
void osd_Log_Net_Initialize(void);

/*@ requires \valid_read(Transmit_Buffer + (0 .. total - 1));
  assigns  reporting_system \from reporting_system, Transmit_Buffer, total;
*/
void osd_Log_Net_Send(uint8_t *Transmit_Buffer, size_t total);

#endif /* __LOG_NET_OSD_H__ */
