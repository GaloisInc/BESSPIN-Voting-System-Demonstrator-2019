/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

#include "crypto.h"

// defaults for cryptographic keys
// these are only linked in for testing purposes and the default SBB
// configuration; otherwise, keys are defined in the per-box SBB
// configuration files

const aes256_key barcode_mac_key = "From Russia with Love";
const aes256_key log_root_block_mac_key = "From Russia with Love";
const aes256_key log_entry_mac_key = "From Russia with Love";
