#include "log_io.h"
#include "../crypto/crypto.h"
#include "debug_io.h"
#include "log_fs.h"
#include "log_net.h"
#include <assert.h>
#include <string.h>

#define portable_assert(x) assert(x)

// Local constants

const secure_log_entry null_secure_log_entry = {{0}, {0}};

///////////////////////////////////////////////////
// Common constants needed by all implemenations //
///////////////////////////////////////////////////

static const char *REQUEST_LINE_1 = "POST /";
static const char *REQUEST_LINE_3 = " HTTP/1.1\r\n";
static const char *HEADER_1 = "Host: 10.6.6.253\r\n";
static const char *HEADER_2 = "User-Agent: sbb/2019\r\n";
static const char *HEADER_3 = "Accept: */*\r\n";
static const char *HEADER_4 = "Content-Type: application/octet-stream\r\n";
static const char *HEADER_5_1 = "Content-Length: ";
static const char *DOUBLE_CRLF = "\r\n\r\n";

// We assume that a log entry data block can't be more than 9_999_999 bytes long, so
// we allocate up to 7 characters for this to be printed in decimal in the HTTP header.
static const size_t worst_case_data_length = 7;

// In order to compute the CBC_AES_MAC of a log entry, we require the full data block
// to be an exact multiple of AES_BLOCK_LENGTH_BYTES long.
//
// We therefore add just the right number of padding spaces between the data
// block and the hash, as computed by the following 3 constants:
const size_t unpadded_log_entry_length =
    LOG_ENTRY_LENGTH + SHA256_BASE_64_DIGEST_LENGTH_BYTES;

const size_t padded_log_entry_length =
    ((unpadded_log_entry_length / AES_BLOCK_LENGTH_BYTES) + 1) *
    AES_BLOCK_LENGTH_BYTES;

const size_t bytes_of_padding_required =
    padded_log_entry_length - unpadded_log_entry_length;

// The total length of a log entry is the length of the padded log entry, plus
// one more space, plus the Base64 MAC data, plus a final two bytes for a \r\n
const size_t total_log_entry_length =
    padded_log_entry_length + 3 + BASE_64_AES_BLOCK_LENGTH_BYTES;

static const char space = ' ';
static const uint8_t carriage_return = '\r';
static const uint8_t new_line = '\n';

/*@ requires \valid(Transmit_Buffer + (0 .. Transmit_Buffer_Length - 1));
    requires valid_string(log_file_name);
    requires \valid(total);
    requires \valid(first_byte_of_data_index);
    requires 1 <= bytes_of_padding_required <= 16;
    requires valid_read_string(REQUEST_LINE_1);
    requires valid_read_string(REQUEST_LINE_3);
    requires valid_read_string(HEADER_1);
    requires valid_read_string(HEADER_2);
    requires valid_read_string(HEADER_3);
    requires valid_read_string(HEADER_4);
    requires valid_read_string(HEADER_5_1);
    requires valid_read_string(DOUBLE_CRLF);
*/
void Prepare_Transmit_Buffer(secure_log_entry the_entry,       // in
                             const char *log_file_name,        // in
                             const size_t http_content_length, // in
                             uint8_t *Transmit_Buffer,         // out by ref
                             size_t *total,                    // out by ref
                             size_t *first_byte_of_data_index, // out by ref
                             size_t Transmit_Buffer_Length);   // in

//////////////////////////////////////////////
// Common Implementation, built on log_fs.h //
//////////////////////////////////////////////

Log_FS_Result Log_IO_Initialize()
{
    log_system_debug_printf("unpadded: %zu", unpadded_log_entry_length);
    log_system_debug_printf("  padded: %zu", padded_log_entry_length);
    log_system_debug_printf("  spaces: %zu", bytes_of_padding_required);

    Log_Net_Initialize();
    return Log_FS_Initialize();
}

Log_FS_Result Log_IO_Create_New(Log_Handle *stream, const char *name,
                                const http_endpoint endpoint)
{
    Log_FS_Result result = Log_FS_Create_New(stream, name);
    stream->endpoint = endpoint;
    log_system_debug_printf("Setting remote file name to %s\n", name);
    stream->remote_file_name = (char *)name;
    return result;
}

Log_FS_Result Log_IO_Open(Log_Handle *stream,           // OUT
                          const char *name,             // IN
                          const http_endpoint endpoint) // IN
{
    Log_FS_Result result = Log_FS_Open(stream, name);

    log_system_debug_printf("Setting open remote file name to %s\n", name);
    stream->remote_file_name = (char *)name;
    stream->endpoint = endpoint;
    return result;
}

Log_FS_Result Log_IO_Close(Log_Handle *stream) // IN
{
    return Log_FS_Close(stream);
}

Log_FS_Result Log_IO_Sync(Log_Handle *stream) // IN
{
    return Log_FS_Sync(stream);
}

bool Log_IO_File_Exists(const char *name) { return Log_FS_File_Exists(name); }

Log_FS_Result Log_IO_Write_Base64_Entry(Log_Handle *stream,
                                        secure_log_entry the_entry)
{
    // Step 1 - Calculate the length of the fixed parts of the HTTP POST Header
    const size_t HTTP_Header_Fixed_Part_Length =
        strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
        strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
        strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    // The length of the HTTP message body is the length of the already-padded
    // log entry, plus the length of the Base64 encoding of an AES_CBC_MAC, plus
    // one extra space between the log entry and the MAC, plus 2 bytes for the final
    // \r\n sequence, so...
    const size_t http_content_length =
        padded_log_entry_length + BASE_64_AES_BLOCK_LENGTH_BYTES + 3;

    const size_t Transmit_Buffer_Length =
        HTTP_Header_Fixed_Part_Length + worst_case_data_length +
        strlen(stream->remote_file_name) + http_content_length;

    uint8_t Transmit_Buffer[Transmit_Buffer_Length];
    size_t total = 0;
    size_t first_byte_of_data_index = 0;

    // Step 2 - Prepare data to be sent, including the HTTP POST
    // header for the network.
    Prepare_Transmit_Buffer(the_entry, stream->remote_file_name,
                            http_content_length, Transmit_Buffer, &total,
                            &first_byte_of_data_index, Transmit_Buffer_Length);

    log_system_debug_printf("total passed back is %zu", total);
    log_system_debug_printf("first byte of data index is %zu", first_byte_of_data_index);

    // Step 3 - Write (data # spaces # base64_hash # space # mac # \r\n) to file
    size_t written =
        Log_FS_Write(stream, &Transmit_Buffer[first_byte_of_data_index],
                     total - first_byte_of_data_index);

    // Step 4 - Write HTTP header plus same data over
    // network to the Reporting System if
    // requested by the client when this log file was initialized.
    if (stream->endpoint != HTTP_Endpoint_None)
    {
        Log_Net_Send(Transmit_Buffer, total);
    }

    if (written == total)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

#pragma GCC diagnostic ignored "-Waggregate-return"
secure_log_entry Log_IO_Read_Base64_Entry(Log_Handle *stream, // IN
                                          size_t n)           // IN
{
    secure_log_entry secure_log_entry_result;
    uint8_t dummy_char;
    size_t olen;
    file_offset original_offset;
    off_t byte_offset_of_entry_n;
    int r;
    base64_secure_log_entry result;
    size_t ret_entry, ret_space, ret_digest;

    //@ assert 1 <= bytes_of_padding_required <= 16;

    byte_offset_of_entry_n = n * total_log_entry_length;

    original_offset = Log_FS_Tell(stream);

    Log_FS_Seek(stream, byte_offset_of_entry_n);

    ret_entry = Log_FS_Read(stream, &result.the_entry[0], LOG_ENTRY_LENGTH);


    /*@
      loop invariant 0 <= space_count <= bytes_of_padding_required;
      loop invariant 1 <= bytes_of_padding_required <= 16;
      loop assigns ret_space, space_count, dummy_char;
      loop variant bytes_of_padding_required - space_count;
    */
    for (size_t space_count = 0; space_count < bytes_of_padding_required;
         space_count++)
    {
        ret_space = Log_FS_Read(stream, &dummy_char, 1);
    }

    ret_digest = Log_FS_Read(stream, &result.the_digest[0],
                             SHA256_BASE_64_DIGEST_LENGTH_BYTES);

    // On the SBB, we neither read nor verify the AES_CBC_MAC that follows
    // the Hash.

    // Restore the original offset
    Log_FS_Seek(stream, original_offset);

    if (ret_entry == LOG_ENTRY_LENGTH &&
        ret_digest == SHA256_BASE_64_DIGEST_LENGTH_BYTES && ret_space == 1)
    {
        // Check for validity of the Base64 encoded hash data and compute
        // the length of the decoded binary hash data.
        r = mbedtls_base64_decode(NULL, 0, &olen, &result.the_digest[0],
                                  SHA256_BASE_64_DIGEST_LENGTH_BYTES);
        if (r == MBEDTLS_ERR_BASE64_BUFFER_TOO_SMALL)
        {
            // Looks like a valid Base64 encoded string, BUT (for example)
            // a base64-encoded hash of 44 characters, _might_ decode to
            // 31, 32, or 33 bytes. We're expecting exactly 32, so we have
            // to check that first to avoid a buffer overflow
            if (olen == SHA256_DIGEST_LENGTH_BYTES)
            {
	        // We still need to decode into a buffer which is larger than
	        // strictly necessary to satisfy the precondition on base64_decode
                uint8_t tmpbuf[SHA256_DIGEST_LENGTH_BYTES + 1];

                r = mbedtls_base64_decode(
                    &tmpbuf[0],
                    SHA256_DIGEST_LENGTH_BYTES + 1, &olen,
                    &result.the_digest[0], SHA256_BASE_64_DIGEST_LENGTH_BYTES);

                if (r == 0)
                {
  		    // All is well... so copy the decoded digest
		    // into secure_log_entry_result.the_digest

                    /*@
                      loop invariant 0 <= i <= SHA256_DIGEST_LENGTH_BYTES;
                      loop assigns i, secure_log_entry_result.the_digest[0 .. SHA256_DIGEST_LENGTH_BYTES - 1];
                      loop variant SHA256_DIGEST_LENGTH_BYTES - i;
                    */
                    for (size_t i = 0; i < SHA256_DIGEST_LENGTH_BYTES; i++)
                    {
                        secure_log_entry_result.the_digest[i] = tmpbuf[i];
                    }

		    // Now copy the data

                    /*@
                      loop invariant 0 <= k <= LOG_ENTRY_LENGTH;
                      loop assigns k, secure_log_entry_result.the_entry[0 .. LOG_ENTRY_LENGTH - 1];
                      loop variant LOG_ENTRY_LENGTH - k;
                    */
                    for (size_t k = 0; k < LOG_ENTRY_LENGTH; k++)
                    {
                        secure_log_entry_result.the_entry[k] =
                            result.the_entry[k];
                    }
                    return secure_log_entry_result;
                }
                else // decode failed
                {

                    log_system_debug_printf("Log_IO_Read_Base64_Entry - decode failed");
                    return null_secure_log_entry;
                }
            }
            else // Decoded hash not the right length
            {
                log_system_debug_printf("Log_IO_Read_Base64_Entry - length wrong");
                return null_secure_log_entry;
            }
        }
        else // Base64 encoded string was just invalid
        {
            log_system_debug_printf("Log_IO_Read_Base64_Entry - Base64 string invalid");
            return null_secure_log_entry;
        }
    }
    // File Reads failed, so...
    log_system_debug_printf("Log_IO_Read_Base64_Entry - reading file failed");
    return null_secure_log_entry;
}

size_t Log_IO_Num_Base64_Entries(Log_Handle *stream)
{
    size_t file_size;
    file_size = Log_FS_Size(stream);

    log_system_debug_printf("file size of log = %d", file_size);

    // The file size _should_ be an exact multiple of
    // the total size of one log entry.
    if ((file_size % total_log_entry_length) == 0)
    {
        return (file_size / total_log_entry_length);
    }
    else
    {
        // If the file isn't an exact multiple of log entries, then assume
        // the file is corrupt and return 0.
        return 0;
    }
}

#pragma GCC diagnostic ignored "-Waggregate-return"
secure_log_entry Log_IO_Read_Last_Base64_Entry(Log_Handle *stream)
{
    size_t N;
    N = Log_IO_Num_Base64_Entries(stream);

    // We cannot get anything from an empty file so
    if (N > 0)
    {
        return Log_IO_Read_Base64_Entry(stream, N - 1);
    }
    else
    {
        return null_secure_log_entry;
    }
}

void Prepare_Transmit_Buffer(secure_log_entry the_entry,       // in
                             const char *log_file_name,        // in
                             const size_t http_content_length, // in
                             uint8_t *Transmit_Buffer,         // out by ref
                             size_t *total,                    // out by ref
                             size_t *first_byte_of_data_index, // out by ref
                             size_t Transmit_Buffer_Length)    // in
{
    size_t olen;
    int r;
    base64_secure_log_entry the_secure_log_entry;

    // To satisfy the precondition of mbedtls_base64_encode, we need
    // a buffer which is 2 bytes longer than strictly necessary, so
    uint8_t base64_digest[SHA256_BASE_64_DIGEST_LENGTH_BYTES + 2];

    // Step 1 - Form the Base64 encoding of the hash
    r = mbedtls_base64_encode(&base64_digest[0],
                              SHA256_BASE_64_DIGEST_LENGTH_BYTES + 2, &olen,
                              &the_entry.the_digest[0],
                              SHA256_DIGEST_LENGTH_BYTES,
                              false); // Don't add final \0

    // Copy the result into the_secure_log_entry
    copy_sha256_base64_digest (&the_secure_log_entry.the_digest[0],
			       &base64_digest[0]);

    (void)r; // suppress warning on r unused.

    assert(SHA256_BASE_64_DIGEST_LENGTH_BYTES == olen);

    // // Step 2 - Copy the data block
    copy_log_entry(&the_secure_log_entry.the_entry[0], &the_entry.the_entry[0]);

    log_system_debug_printf("Transmit_Buffer is %zu bytes long", Transmit_Buffer_Length);

    log_system_debug_printf("HTTP Content-Length is %zu bytes", http_content_length);

    // Initialize Transmit_Buffer to all 0x00 so we can dynamically calculate the
    // length of the header
    /*@
      loop invariant 0 <= i <= Transmit_Buffer_Length;
      loop invariant \valid(Transmit_Buffer + (0 .. Transmit_Buffer_Length - 1));
      loop assigns i, Transmit_Buffer[0 .. Transmit_Buffer_Length - 1];
      loop variant Transmit_Buffer_Length - i;
    */
    for (size_t i = 0; i < Transmit_Buffer_Length; i++)
    {
        Transmit_Buffer[i] = 0x00;
    }

    snprintf((char *)Transmit_Buffer, Transmit_Buffer_Length,
	     "%s%s%s%s%s%s%s%s%zu%s",
             REQUEST_LINE_1, log_file_name,
             REQUEST_LINE_3, HEADER_1, HEADER_2, HEADER_3, HEADER_4, HEADER_5_1,
             http_content_length, DOUBLE_CRLF);

    //@ assert valid_read_string((char *) Transmit_Buffer);

    // After the header has been written, we have N bytes of header,
    // occupying bytes 0 .. (N-1) of Transmit_Buffer. So.. the first byte of the
    // data block will be at index N. We can use strlen to compute
    // this since Transmit_Buffer was previously populated with all 0x00 bytes.
    *first_byte_of_data_index = strlen((char *)Transmit_Buffer);
    log_system_debug_printf("Length of header block is %zu", *first_byte_of_data_index);

    // Add the_secure_log_entry.the_entry to the Transmit_Buffer
    copy_log_entry(&Transmit_Buffer[*first_byte_of_data_index],
                   &the_secure_log_entry.the_entry[0]);

    // Add just the right number of spaces to make the data block,
    // spaces, hash and new_line an exact multiple of 16 bytes long.
    size_t space_index = *first_byte_of_data_index + LOG_ENTRY_LENGTH;
    log_system_debug_printf("space index is %zu", space_index);
    /*@
      loop invariant 0 <= space_count <= bytes_of_padding_required;
      loop assigns space_index, space_count,
           Transmit_Buffer[0 .. bytes_of_padding_required - 1];
      loop variant bytes_of_padding_required - space_count;
    */
    for (size_t space_count = 0; space_count < bytes_of_padding_required;
         space_count++)
    {
        Transmit_Buffer[space_index] = space;
        space_index++;
    }

    // Add the Base64 encoded hash value from the_secure_log_entry.the_digest
    size_t hash_index = space_index;
    log_system_debug_printf("hash index is %zu", hash_index);
    copy_sha256_base64_digest(&Transmit_Buffer[hash_index],
			      &the_secure_log_entry.the_digest[0]);

    //    size_t new_line_index = hash_index + SHA256_BASE_64_DIGEST_LENGTH_BYTES;
    size_t second_space_index = hash_index + SHA256_BASE_64_DIGEST_LENGTH_BYTES;
    log_system_debug_printf("second space index is %zu", second_space_index);
    Transmit_Buffer[second_space_index] = space;

    // The total length of the data block, spaces, hash
    // should be as expected and should be a multiple of AES_BLOCK_LENGTH_BYTES
    portable_assert((second_space_index - *first_byte_of_data_index) ==
                    padded_log_entry_length);
    portable_assert(padded_log_entry_length % AES_BLOCK_LENGTH_BYTES == 0);

    // Compute the AES_CBC_MAC of the whole block
    aes128_block binary_mac;
    aes_cbc_mac(&Transmit_Buffer[*first_byte_of_data_index],
                padded_log_entry_length,
                &binary_mac[0],
                Log_Entry_MAC_Key);

    // Turn that MAC into Base64 format.
    // To satisfy the precondition of mbedtls_base64_encode, we need
    // a buffer which is 2 bytes longer than strictly necessary, so
    uint8_t base64_mac[BASE_64_AES_BLOCK_LENGTH_BYTES + 2];

    r = mbedtls_base64_encode(&base64_mac[0],
                              BASE_64_AES_BLOCK_LENGTH_BYTES + 2, &olen,
                              &binary_mac[0], AES_BLOCK_LENGTH_BYTES,
                              false); // Don't add final \0
    (void)r;                          // suppress warning on r unused.

    portable_assert(BASE_64_AES_BLOCK_LENGTH_BYTES == olen);

    // And append that MAC to the data to be sent
    size_t first_mac_index = second_space_index + 1;

    log_system_debug_printf("first mac index is %zu", first_mac_index);

    copy_base64_aes128_block (&Transmit_Buffer[first_mac_index], &base64_mac[0]);

    // add \r\n
    size_t first_lineend_index =
        first_mac_index + BASE_64_AES_BLOCK_LENGTH_BYTES;
    log_system_debug_printf("first line-ending index is %zu", first_lineend_index);
    Transmit_Buffer[first_lineend_index] = carriage_return;
    Transmit_Buffer[first_lineend_index + 1] = new_line;

    // If the final byte is at offset (first_lineend_index + 1) in Transmit_Buffer,
    // then the current of bytes is (first_lineend_index + 2)
    *total = first_lineend_index + 2;

    log_system_debug_printf("total bytes to send is %zu", *total);
    return;
}
