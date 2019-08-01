/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"
#include "FreeRTOSIPConfig.h"

// Default configuration strings for a SBB
/* MAC address of the box */
#define sbb_realMAC_ADDR0		0x00
#define sbb_realMAC_ADDR1		0x0a
#define sbb_realMAC_ADDR2		0x35
#define sbb_realMAC_ADDR3		0x66
#define sbb_realMAC_ADDR4		0x66
#define sbb_realMAC_ADDR5		0x07

// IP address of SBB in case DHCP fails.  
#define sbbIP_ADDR0		10
#define sbbIP_ADDR1		88
#define sbbIP_ADDR2		88
#define sbbIP_ADDR3		2

const char *sbb_name = "DEFAULT";
const log_name system_log_file_name = "default_system.log";
const log_name app_log_file_name = "default_application.log";

const uint8_t sbb_mac_address[6] = { sbb_realMAC_ADDR0, sbb_realMAC_ADDR1, sbb_realMAC_ADDR2, sbb_realMAC_ADDR3, sbb_realMAC_ADDR4, sbb_realMAC_ADDR5 };
const uint8_t sbb_default_ip_address[4] = { sbbIP_ADDR0, sbbIP_ADDR1, sbbIP_ADDR2, sbbIP_ADDR3 };
const uint8_t sbb_default_netmask[4] = { configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 };
const uint8_t sbb_default_gateway_address[4] = { configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3 };
const uint8_t sbb_default_dns_server_address[4] = { configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3 };
