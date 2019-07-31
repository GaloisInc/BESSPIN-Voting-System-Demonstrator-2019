/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"

// Configuration strings for SBB 1
const char *sbb_name = "SBB4";
const log_name system_log_file_name = "sbb4_system.log";
const log_name app_log_file_name = "sbb4_application.log";
const uint8_t sbb_mac_address[6] = { 0x00, 0x0a, 0x35, 0x66, 0x66, 0x04 };
const uint8_t sbb_default_ip_address[4] = { 10, 5, 5, 104 };
const uint8_t sbb_default_netmask[4] = { 255, 255, 255, 0 };
const uint8_t sbb_default_gateway_address[4] = { 10, 5, 5, 104 };
const uint8_t sbb_default_dns_server_address[4] = { 10, 5, 5, 104 };

// cryptographic keys for SBB 1

const aes256_key barcode_mac_key = "From Russia with Love";
const aes256_key log_root_block_mac_key = "Tomorrow Never Dies";
const aes256_key log_entry_mac_key = "Quantum of Solace";