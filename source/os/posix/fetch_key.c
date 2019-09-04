#include "votingdefs.h"
#include "crypto/crypto.h"
// All software implementation of AES. To be replaced when hardware HSM is available
#include "crypto/aes.h"
// All software implementation of SHA2. To be replaced when hardware HSM is available
#include "crypto/sha2-openbsd.h"

extern aes256_key mock_key;
const uint8_t *osd_fetch_key (AES_Key_Name key)
{
    (void)key;
    return mock_key;
}
