#include "sbb_crypto.h"
#include "crypto.h"
#include "base64.h"
#include <assert.h>
#include <string.h>

#ifdef TARGET_OS_FreeRTOS
#include "FreeRTOS_Sockets.h"
#define htonl FreeRTOS_htonl
#else
#include <arpa/inet.h>
#endif

// Needed for checking barcode validity
#define TIMESTAMP_LENGTH_BYTES 4
#define ENCRYPTED_BALLOT_LENGTH_BYTES (AES_BLOCK_LENGTH_BYTES)
#define BASE64_DECODED_BYTES 33 // From formula in cryptol spec

#define TIMESTAMP_DIGITS 10
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
    // timeBytes # encryptedBallot.
    // `encryptedBallot` is bytes 0-15 of the base64 decoding.
    uint8_t our_digest_input[CBC_MAC_MESSAGE_BYTES] = {0};
    uint8_t our_digest_output[AES_BLOCK_LENGTH_BYTES] = {0};
    // (a) Calculate the time bytes
    unsigned timeBytes = 0;
    assert(sizeof(timeBytes) >= TIMESTAMP_LENGTH_BYTES);
    {
        unsigned pow = 1;
        for (int b = TIMESTAMP_DIGITS - 1; b >= 0; b--) {
            timeBytes += pow*(barcode[b] - 48); /*Time is in ascii decimal */
            pow *= 10;
        }
    }

    // (b) copy time bytes to first TIMESTAMP_LENGTH_BYTES of message to cbc-mac
    timeBytes = htonl(timeBytes);
    memcpy(&our_digest_input[0], &timeBytes, TIMESTAMP_LENGTH_BYTES);

    // (c) copy encrypted ballot to our input
    memcpy(&our_digest_input[TIMESTAMP_LENGTH_BYTES], &decoded_barcode[0], ENCRYPTED_BALLOT_LENGTH_BYTES);

    // 3. Compute the cbc-mac
    aes_cbc_mac(&our_digest_input[0], CBC_MAC_MESSAGE_BYTES, // Input
                &our_digest_output[0]);                        // Output

    // 4.
    // Compare computed digest against cbc-mac in the barcode
    bool b_match = true;
    for (size_t i = 0; b_match && (i < AES_BLOCK_LENGTH_BYTES); ++i) {
        b_match &= (our_digest_output[i] == decoded_barcode[i + ENCRYPTED_BALLOT_LENGTH_BYTES]);
    }

    return b_match;
}
