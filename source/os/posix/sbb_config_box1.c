/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */
#include "sbb.h"

// Configuration strings for SBB 1
const char *sbb_name = "SBB1";
const log_name system_log_file_name = "sbb1_system.log";
const log_name app_log_file_name = "sbb1_application.log";

const aes256_key barcode_mac_key = "From Russia with Love";
const aes256_key log_root_block_mac_key = "On Her Majesty's Secret Service";
const aes256_key log_entry_mac_key = "Diamonds are Forever";
