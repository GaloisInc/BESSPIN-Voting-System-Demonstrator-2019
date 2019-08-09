#include "sbb_crypto.h"
#include "base64.h"
#include "crypto.h"
#include "sbb.h"
#include <assert.h>
#include <string.h>

// From mbedtls precondition.
#define BASE64_DECODED_BUFFER_BYTES (3 * (BASE64_ENCODED_LENGTH / 4))

#define BASE64_ENCODING_START (TIMESTAMP_LENGTH_BYTES + 1)

#define CBC_MAC_INPUT_DATA_LENGTH_BYTES                                        \
    (TIMESTAMP_LENGTH_BYTES + ENCRYPTED_BALLOT_LENGTH_BYTES)
#define CBC_MAC_MESSAGE_LENGTH_BYTES                                           \
    (((CBC_MAC_INPUT_DATA_LENGTH_BYTES) + (AES_BLOCK_LENGTH_BYTES - 1)) &      \
     (~(AES_BLOCK_LENGTH_BYTES - 1)))

bool timestamp_lte_now(const uint8_t *barcode_time)
{
#ifdef SIMULATION_UART
    // no time validation in the UART simulation, always return true
    (void) barcode_time;
    return true;
#else // SIMULATION_UART
    uint32_t year, year_now;
    uint16_t month, day, hour, minute;
    uint16_t month_now, day_now, hour_now, minute_now;

    // the format string needs to be different on platforms where long is 32
    // bits (4 bytes), in order to avoid a compiler warning
    const char *format_string =
        (sizeof(long) == 4) ? "%lu+%hu+%hu+%hu+%hu" : "%u+%hu+%hu+%hu+%hu";

    int num_scanned = sscanf((const char *)barcode_time, format_string, &year,
                             &month, &day, &hour, &minute);
    bool b_valid = false;
    if (num_scanned == 5)
    {
#ifdef HARDCODE_CURRENT_TIME
        year_now = CURRENT_YEAR;
        month_now = CURRENT_MONTH;
        day_now = CURRENT_DAY;
        hour_now = CURRENT_HOUR;
        minute_now = CURRENT_MINUTE;
#else
        get_current_time(&year_now, &month_now, &day_now, &hour_now,
                         &minute_now);
#endif /* HARDCODE_CURRENT_TIME */
        bool b_valid_by_minutes = minute >= minute_now;
        bool b_valid_by_hours =
            hour > hour_now || (hour == hour_now && b_valid_by_minutes);
        bool b_valid_by_days =
            day > day_now || (day == day_now && b_valid_by_hours);
        bool b_valid_by_months =
            month > month_now || (month == month_now && b_valid_by_days);
        bool b_valid_by_years =
            year > year_now || (year == year_now && b_valid_by_months);

        b_valid = b_valid_by_years;
    }

    return b_valid;
#endif // SIMULATION_UART
}

barcode_validity crypto_check_barcode_valid(barcode_t the_barcode,
                                            barcode_length_t length)
{
    /**
       timeDigits # ":" # encodeBase64 (encryptedBallot # auth)
    */
    int r;
    size_t olen;
    barcode_validity result = BARCODE_INVALID_OTHER;

    // 0.
    // Precondition: BASE64_ENCODING_START < length &&
    //               (length - BASE64_ENCODING_START) == BASE64_ENCODED_LENGTH
    debug_printf("crypto_check_barcode_valid: checking barcode length (%d)\r\n", length);
    if (BASE64_ENCODING_START < length &&
        (length - BASE64_ENCODING_START) == BASE64_ENCODED_LENGTH)
    {
        debug_printf("crypto_check_barcode_valid: base64 decoding\r\n");
        // 1.
        // Decode. mbedtls_base64_decode requires (srcLength/4)*3 bytes in the destination.
        uint8_t decoded_barcode[BASE64_DECODED_BUFFER_BYTES] = {0};
        r = mbedtls_base64_decode(
            &decoded_barcode[0], BASE64_DECODED_BUFFER_BYTES, &olen,
            (const unsigned char *)&the_barcode[BASE64_ENCODING_START],
            BASE64_ENCODED_LENGTH);

        if (r == 0 && BASE64_DECODED_BYTES == olen)
        {
#ifndef SIMULATION_UART
            debug_printf("crypto_check_barcode_valid: checking timestamp\r\n");
#endif // SIMULATION_UART
            // 2. a
            // Check the timestamp to make sure it's not from the future

            // The barcode must not have expired (i.e. the expiry date should be > now)
            if (timestamp_lte_now((const uint8_t *)&the_barcode[0]))
            {
                // 2. b
                // Now set up the message for aes_cbc_mac. The formula is:
                // timestamp # encryptedBallot.
                // `encryptedBallot` is bytes 0-15 of the base64 decoding.
                uint8_t our_digest_input[CBC_MAC_MESSAGE_LENGTH_BYTES] = {0};
                uint8_t our_digest_output[AES_BLOCK_LENGTH_BYTES] = {0};
                // { input |-> ... }
                memcpy(&our_digest_input[0], &the_barcode[0],
                       TIMESTAMP_LENGTH_BYTES);
                // { input[0..15] |-> timestamp[0..5] }
                memcpy(&our_digest_input[TIMESTAMP_LENGTH_BYTES],
                       &decoded_barcode[0], ENCRYPTED_BALLOT_LENGTH_BYTES);
                // { input[0..32] |-> timestamp[0..5] # decode_barcode[0..15] }

                // 3.
                // Compute the cbc-mac
                aes_cbc_mac(&our_digest_input[0], CBC_MAC_MESSAGE_LENGTH_BYTES,
                            &our_digest_output[0], Barcode_MAC_Key);

                // 4.
                // Compare computed digest against cbc-mac in the barcode
                if (0 == memcmp(&our_digest_output[0],
                                &decoded_barcode[ENCRYPTED_BALLOT_LENGTH_BYTES],
                                AES_BLOCK_LENGTH_BYTES))
                {
                    result = BARCODE_VALID;
                }
                else
                {
                    result = BARCODE_INVALID_SIGNATURE;
                }
            }
            else
            {
                result = BARCODE_INVALID_TIMESTAMP;
            }
        }
        else
        {
            result = BARCODE_INVALID_ENCODING;
        }
    }
    else
    {
        result = BARCODE_INVALID_LENGTH;
    }
    return result;
}
