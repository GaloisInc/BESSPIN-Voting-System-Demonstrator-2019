///////////////////////////////////////////////////////
// Common include files needed by all implemenations //
///////////////////////////////////////////////////////

#include "crypto/crypto.h"
#include "logging/log_net.h"
#include "logging/debug_io.h"
#include "logging/log_io.h"
#include "votingdefs.h"

#include <stdio.h>

void osd_Log_Net_Initialize(void) { 
    osd_assert(0);
    return; 
}

void osd_Log_Net_Send(uint8_t *Transmit_Buffer, size_t total) {
  (void) Transmit_Buffer;
  (void) total;
    osd_assert(0);
    return; 
}
