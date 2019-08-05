/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

#include "crypto.h"

// defaults for cryptographic keys
// these are only linked in for testing purposes and the default SBB
// configuration; otherwise, keys are defined in the per-box SBB
// configuration files

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
const aes256_key log_root_block_mac_key = "From Russia with Love";
const aes256_key log_entry_mac_key = "From Russia with Love";
