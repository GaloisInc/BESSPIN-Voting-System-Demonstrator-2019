///////////////////////////////////////////////////////
// Common include files needed by all implemenations //
///////////////////////////////////////////////////////

#include "crypto/crypto.h"
#include "logging/log_net.h"
#include "logging/debug_io.h"
#include "logging/log_io.h"

#include <stdio.h>

uint32_t ulApplicationGetNextSequenceNumber(uint32_t ulSourceAddress,
                                            uint16_t usSourcePort,
                                            uint32_t ulDestinationAddress,
                                            uint16_t usDestinationPort);


//////////////////////////////////////////////
// FreeRTOS-specific includes and constants //
//////////////////////////////////////////////

/* FreeRTOS and IP stack includes. */
#include "FreeRTOS.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "list.h"

#include "sbb_freertos.h"

#define portable_assert(x) configASSERT(x)

extern const uint16_t sbb_log_port_number;

//////////////////////////////
// Exported function bodies //
//////////////////////////////

#ifdef NETWORK_LOGS
void osd_Log_Net_Initialize()
{
    // On FreeRTOS, this is currently null.
    //
    // We assume that FreeRTOS_IPInit() has been called already
    // by the main program.
    return;
}

// Send network logs in simulation as well
void osd_Log_Net_Send(uint8_t *Transmit_Buffer, size_t total)
{
      // Send the data to the network logging taks
      #ifdef NETWORK_LOG_DEBUG
      debug_printf("Log_Net_Send: %lu bytes\r\n", total);
      #endif
      size_t res = xStreamBufferSend(xNetLogStreamBuffer,
                        (void *)Transmit_Buffer,
                        total,
                        0);
      if (res != total) {
        printf("Log_Net_Send Warning: attempted to send %u bytes, but sent only %u\r\n", total, res);
      }
}
#else // NETWORK_LOGS

void osd_Log_Net_Initialize(void) { return; }

void osd_Log_Net_Send(uint8_t *Transmit_Buffer, size_t total) {
  (void) Transmit_Buffer;
  (void) total;
}
#endif //NETWORK_LOGS
