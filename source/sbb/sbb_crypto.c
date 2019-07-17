#include "sbb_crypto.h"
#include "crypto.h"
#include "base64.h"
#include <assert.h>
#include <string.h>

// Needed for checking barcode validity
#define TIMESTAMP_LENGTH_BYTES 16
#define ENCRYPTED_BALLOT_LENGTH_BYTES (AES_BLOCK_LENGTH_BYTES)
#define BASE64_DECODED_BYTES 32 // From formula in cryptol spec

#define TIMESTAMP_DIGITS 16
#define BASE64_ENCODING_START (TIMESTAMP_DIGITS + 1)

#define CBC_MAC_INPUT_DATA_BYTES \
    (TIMESTAMP_LENGTH_BYTES + ENCRYPTED_BALLOT_LENGTH_BYTES)
#define CBC_MAC_MESSAGE_BYTES \
  (((CBC_MAC_INPUT_DATA_BYTES) + (AES_BLOCK_LENGTH_BYTES-1)) & (~(AES_BLOCK_LENGTH_BYTES - 1)))

bool crypto_check_barcode_valid(barcode_t barcode, barcode_length_t length) {
    /**
       timeDigits # ":" # encodeBase64 (encryptedBallot # auth)
    */
    int r;
    size_t olen;
    // 1.
    // Decode. mbedtls_base64_decode requires (srcLength/4)*3 bytes in the destination.
    uint8_t decoded_barcode[BASE64_DECODED_BYTES + 1] = {0};
    r = mbedtls_base64_decode(&decoded_barcode[0],
                              BASE64_DECODED_BYTES + 1,
                              &olen,
                              &barcode[BASE64_ENCODING_START],
                              length - BASE64_ENCODING_START);

    if (BASE64_DECODED_BYTES != olen) {
        return false;
    }

    // 2.
    // Now set up the message for aes_cbc_mac. The formula is:
    // timestamp # encryptedBallot.
    // `encryptedBallot` is bytes 0-15 of the base64 decoding.
    uint8_t our_digest_input[CBC_MAC_MESSAGE_BYTES] = {0};
    uint8_t our_digest_output[AES_BLOCK_LENGTH_BYTES] = {0};
    memcpy(&our_digest_input[0], &barcode[0], TIMESTAMP_LENGTH_BYTES);

    memcpy(&our_digest_input[TIMESTAMP_LENGTH_BYTES], &decoded_barcode[0], ENCRYPTED_BALLOT_LENGTH_BYTES);

    // 3. Compute the cbc-mac
    aes_cbc_mac(&our_digest_input[0], CBC_MAC_MESSAGE_BYTES, // Input
                &our_digest_output[0]);                      // Output

    // 4.
    // Compare computed digest against cbc-mac in the barcode
    bool b_match = true;
    for (size_t i = 0; b_match && (i < AES_BLOCK_LENGTH_BYTES); ++i) {
        b_match &= (our_digest_output[i] == decoded_barcode[i + ENCRYPTED_BALLOT_LENGTH_BYTES]);
    }

    return b_match;
}
