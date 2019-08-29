#include "votingdefs.h"
#include "crypto/crypto.h"
// All software implementation of AES. To be replaced when hardware HSM is available
#include "crypto/aes.h"
// All software implementation of SHA2. To be replaced when hardware HSM is available
#include "crypto/sha2-openbsd.h"

extern aes256_key mock_key;
const uint8_t *osd_fetch_key (AES_Key_Name key)
{
    const uint8_t *result;
    // we simply return addresses of the hard-coded keys that were linked
    // in at compile time, with the mock key returned in any situation
    // where one of the 3 "real" keys is not asked for
    switch (key) {
    case Barcode_MAC_Key:
        result = &barcode_mac_key[0];
        break;

    case Log_Root_Block_MAC_Key:
        result = &log_root_block_mac_key[0];
        break;

    case Log_Entry_MAC_Key:
        result = &log_entry_mac_key[0];
        break;

    default:
        result = &mock_key[0];
        break;
    }

    return result;
}
