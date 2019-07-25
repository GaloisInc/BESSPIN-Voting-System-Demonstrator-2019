/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"

// Default configuration strings for a SBB
const char *sbb_name = "SBB";
const uint8_t sbb_mac_address[6] = { 0x00, 0x0a, 0x35, 0x66, 0x66, 0x00 };
const uint8_t sbb_default_ip_address[4] = { 10, 5, 5, 1 };
const uint8_t sbb_default_netmask[4] = { 255, 255, 255, 0 };
const uint8_t sbb_default_gateway_address[4] = { 10, 5, 5, 1 };
const uint8_t sbb_default_dns_server_address[4] = { 10, 5, 5, 1 };
