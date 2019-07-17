#include "sbb_crypto.h"
#include "crypto.h"
#include "base64.h"
#include <assert.h>
#include <string.h>

// From mbedtls precondition.
#define BASE64_DECODED_BUFFER_BYTES (3*(BASE64_ENCODED_LENGTH / 4))

#define BASE64_ENCODING_START (TIMESTAMP_LENGTH_BYTES + 1)

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
    bool b_match = false;
    // 0.
    // Precondition: length > BASE64_ENCODING_START
    if ( BASE64_ENCODING_START < length  ) {
        // 1.
        // Decode. mbedtls_base64_decode requires (srcLength/4)*3 bytes in the destination.
        // If `length` is not what we are expecting, then this we will return false.
        uint8_t decoded_barcode[BASE64_DECODED_BUFFER_BYTES] = {0};
        r = mbedtls_base64_decode(&decoded_barcode[0],
                                  BASE64_DECODED_BUFFER_BYTES,
                                  &olen,
                                  &barcode[BASE64_ENCODING_START],
                                  length - BASE64_ENCODING_START);

        if (BASE64_DECODED_BYTES == olen) {
            // 2.
            // Now set up the message for aes_cbc_mac. The formula is:
            // timestamp # encryptedBallot.
            // `encryptedBallot` is bytes 0-15 of the base64 decoding.
            uint8_t our_digest_input[CBC_MAC_MESSAGE_BYTES] = {0};
            uint8_t our_digest_output[AES_BLOCK_LENGTH_BYTES] = {0};
            // { input |-> ... }
            memcpy(&our_digest_input[0],
                   &barcode[0],
                   TIMESTAMP_LENGTH_BYTES);
            // { input[0..15] |-> timeestamp[0..5] }
            memcpy(&our_digest_input[TIMESTAMP_LENGTH_BYTES],
                   &decoded_barcode[0],
                   ENCRYPTED_BALLOT_LENGTH_BYTES);
            // { input[0..32] |-> timeestamp[0..5] # decode_barcode[0..15] }

            // 3.
            // Compute the cbc-mac
            aes_cbc_mac(&our_digest_input[0],
                        CBC_MAC_MESSAGE_BYTES,
                        &our_digest_output[0]);

            // 4.
            // Compare computed digest against cbc-mac in the barcode
            b_match = true;
            for (size_t i = 0; b_match && (i < AES_BLOCK_LENGTH_BYTES); ++i) {
                b_match &= (our_digest_output[i] == decoded_barcode[i + ENCRYPTED_BALLOT_LENGTH_BYTES]);
            }
        }

    }
    return b_match;
}
