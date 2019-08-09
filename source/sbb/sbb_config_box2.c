/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */
#include "sbb.h"
#include "FreeRTOSIPConfig.h"

// Default configuration strings for a SBB
/* MAC address of the box */
#define sbb_realMAC_ADDR0		0x10
#define sbb_realMAC_ADDR1		0x0a
#define sbb_realMAC_ADDR2		0x35
#define sbb_realMAC_ADDR3		0x04
#define sbb_realMAC_ADDR4		0xdb
#define sbb_realMAC_ADDR5		0x03

// IP address of SBB in case DHCP fails.  
#define sbbIP_ADDR0		10
#define sbbIP_ADDR1		88
#define sbbIP_ADDR2		88
#define sbbIP_ADDR3		4

// Configuration strings for SBB 2
const char *sbb_name = "SBB2";
const log_name system_log_file_name = "sbb2_system.log";
const log_name app_log_file_name = "sbb2_application.log";

const uint8_t sbb_mac_address[6] = { sbb_realMAC_ADDR0, sbb_realMAC_ADDR1, sbb_realMAC_ADDR2, sbb_realMAC_ADDR3, sbb_realMAC_ADDR4, sbb_realMAC_ADDR5 };
const uint8_t sbb_default_ip_address[4] = { sbbIP_ADDR0, sbbIP_ADDR1, sbbIP_ADDR2, sbbIP_ADDR3 };
const uint8_t sbb_default_netmask[4] = { configNET_MASK0, configNET_MASK1, configNET_MASK2, configNET_MASK3 };
const uint8_t sbb_default_gateway_address[4] = { configGATEWAY_ADDR0, configGATEWAY_ADDR1, configGATEWAY_ADDR2, configGATEWAY_ADDR3 };
const uint8_t sbb_default_dns_server_address[4] = { configDNS_SERVER_ADDR0, configDNS_SERVER_ADDR1, configDNS_SERVER_ADDR2, configDNS_SERVER_ADDR3 };

// cryptographic keys for SBB 2

// NOTE: these are not the real AES keys that will be used in the smart
// ballot box demonstration; cryptographic keys should, in general, never
// be embedded in source code. They exist here for two reasons:
// 1. they make internal smoke testing of the cryptographic subsystem
//    easier, by making it unnecessary for us to provision new internal
//    testing keys at every test run.
// 2. for the 2019 secure hardware demonstration, keys are being stored
//    in the memory image of the software to explicitly provide a
//    target that can be protected by the secure hardware; these
//    definitions enable the cryptographic subsystem to locate them.
// While the depoloyed demonstration systems will have cryptographic
// keys in their memory images, and they will be defined using the same
// symbols, they will _not_ be the keys in this header file (or anywhere
// in the public repository).

const aes256_key barcode_mac_key = "From Russia with Love";
const aes256_key log_root_block_mac_key = "The Man with the Golden Gun";
const aes256_key log_entry_mac_key = "The Spy Who Loved Me";
