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
const aes256_key log_root_block_mac_key = "Tomorrow Never Dies";
const aes256_key log_entry_mac_key = "Quantum of Solace";
