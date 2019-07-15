#ifndef __LOG_NET_H__
#define __LOG_NET_H__

#include "log_net_t.h"
#include "secure_log_t.h"

// Abstract ghost state representing the overall state
// of the reporting system

//@ ghost int reporting_system;

// ACSL Contracts TBD
void Log_Net_Initialize(void);

// ACSL Contracts TBD
void Log_Net_Send(uint8_t *Transmit_Buffer, size_t total);

#endif /* __LOG_NET_H__ */
