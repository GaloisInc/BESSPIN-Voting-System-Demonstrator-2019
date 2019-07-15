#include "log_io.h"
#include "debug_io.h"
#include "log_fs.h"
#include "log_net.h"
#include <assert.h>
#include <string.h>
#include "../crypto/crypto.h"

#define portable_assert(x) assert(x)

// Local constants
const secure_log_entry null_secure_log_entry = {{0}, {0}};
///////////////////////////////////////////////////
// Common constants needed by all implemenations //
///////////////////////////////////////////////////

static const char space = ' ';
// static const char new_line = '\n';

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
const size_t unpadded_log_entry_length = LOG_ENTRY_LENGTH + SHA256_BASE_64_DIGEST_LENGTH_BYTES + 1;

const size_t padded_log_entry_length =
  ((unpadded_log_entry_length / AES_BLOCK_LENGTH_BYTES) + 1) * AES_BLOCK_LENGTH_BYTES;

const size_t bytes_of_padding_required = padded_log_entry_length - unpadded_log_entry_length;


static const uint8_t spaces[AES_BLOCK_LENGTH_BYTES] = "                ";
static const uint8_t new_line = '\n';

//////////////////////////////////////////////
// Common Implementation, built on log_fs.h //
//////////////////////////////////////////////

Log_FS_Result Log_IO_Initialize()
{
    debug_printf ("unpadded: %zu", unpadded_log_entry_length);
    debug_printf ("  padded: %zu", padded_log_entry_length);
    debug_printf ("  spaces: %zu", bytes_of_padding_required);

    Log_Net_Initialize();
    return Log_FS_Initialize();
}

Log_FS_Result Log_IO_Create_New(Log_Handle *stream,
                                const char *name,
                                const http_endpoint endpoint)
{
    Log_FS_Result result = Log_FS_Create_New(stream, name);
    stream->endpoint = endpoint;
    debug_printf ("Setting remote file name to %s\n", name);
    stream->remote_file_name = (char *) name;
    return result;
}

Log_FS_Result Log_IO_Open(Log_Handle *stream, // OUT
                          const char *name)   // IN
{
    Log_FS_Result result = Log_FS_Open(stream, name);

    // TBD set endpoint here?

    debug_printf ("Setting open remote file name to %s\n", name);
    stream->remote_file_name = (char *) name;
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
    size_t olen;
    int r;
    size_t written;
    base64_secure_log_entry base_64_current_entry;
   
    // Calculate the length of the fixed parts of the HTTP POST Header
    const size_t FIXED_MESSAGE_SIZE =
        strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
        strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
        strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    const size_t content_length =
        padded_log_entry_length + BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH;

    const size_t MESSAGE_SIZE = FIXED_MESSAGE_SIZE + worst_case_data_length +
                                strlen(stream -> remote_file_name) + content_length;

    uint8_t Transmit_Buffer[MESSAGE_SIZE];
    size_t total = 0;

    // // Step 1 - Form the Base64 encoding of the hash
    r = mbedtls_base64_encode(&base_64_current_entry.the_digest[0],
                              SHA256_BASE_64_DIGEST_LENGTH_BYTES + 2, &olen,
                              &the_entry.the_digest[0],
                              SHA256_DIGEST_LENGTH_BYTES);
    (void)r; // suppress warning on r unused.
    assert(SHA256_BASE_64_DIGEST_LENGTH_BYTES == olen);

    // // Step 2 - Copy the data block
    memcpy(&base_64_current_entry.the_entry[0], &the_entry.the_entry[0],
           LOG_ENTRY_LENGTH);

    // // Step 3 - Write (data # spaces # base64_hash # new_line) to file
    written = Log_FS_Write(stream, &base_64_current_entry.the_entry[0],
                           LOG_ENTRY_LENGTH);

    // // Write just to right number of spaces, as computed above
    written += Log_FS_Write(stream, spaces, bytes_of_padding_required);

    written += Log_FS_Write(stream, &base_64_current_entry.the_digest[0],
                            SHA256_BASE_64_DIGEST_LENGTH_BYTES);
    written += Log_FS_Write(stream, &new_line, 1);

    Prepare_Transmit_Buffer(base_64_current_entry,
                            padded_log_entry_length,
                            bytes_of_padding_required,
                            stream->endpoint,
                            stream->remote_file_name, 
                            Transmit_Buffer, total, MESSAGE_SIZE);

    // Step 4 - Write same data over network to the Reporting System
    Log_Net_Send (Transmit_Buffer, total);

    if (written == padded_log_entry_length)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

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
    size_t ret_entry, ret_space, ret_digest, ret_new_line;

    byte_offset_of_entry_n = n * padded_log_entry_length;

    original_offset = Log_FS_Tell(stream);

    Log_FS_Seek(stream, byte_offset_of_entry_n);

    ret_entry = Log_FS_Read(stream, &result.the_entry[0], LOG_ENTRY_LENGTH);

    for (size_t space_count = 0; space_count < bytes_of_padding_required; space_count++)
      {
        ret_space = Log_FS_Read(stream, &dummy_char, 1);
      }

    ret_digest = Log_FS_Read(stream, &result.the_digest[0],
                             SHA256_BASE_64_DIGEST_LENGTH_BYTES);
    ret_new_line = Log_FS_Read(stream, &dummy_char, 1);

    // Restore the original offset
    Log_FS_Seek(stream, original_offset);

    if (ret_entry == LOG_ENTRY_LENGTH &&
        ret_digest == SHA256_BASE_64_DIGEST_LENGTH_BYTES && ret_space == 1 &&
        ret_new_line == 1)
    {
        // decode, create secure_log_entry and return
        r = mbedtls_base64_decode(&secure_log_entry_result.the_digest[0],
                                  SHA256_DIGEST_LENGTH_BYTES + 1, &olen,
                                  &result.the_digest[0],
                                  SHA256_BASE_64_DIGEST_LENGTH_BYTES);
        (void)r; // suppress warning on r unused.

        /*@
          loop invariant 0 <= i <= LOG_ENTRY_LENGTH;
          loop invariant \forall size_t j; 0 <= j < i ==> secure_log_entry_result.the_entry[i] == result.the_entry[i];
          loop assigns i, secure_log_entry_result.the_entry[0 .. LOG_ENTRY_LENGTH - 1];
          loop variant LOG_ENTRY_LENGTH - i;
       */
        for (size_t i = 0; i < LOG_ENTRY_LENGTH; i++)
        {
            secure_log_entry_result.the_entry[i] = result.the_entry[i];
        }
        return secure_log_entry_result;
    }
    return null_secure_log_entry;
}

size_t Log_IO_Num_Base64_Entries(Log_Handle *stream)
{
    size_t file_size;
    file_size = Log_FS_Size(stream);

    debug_printf("file size of log = %d", file_size);
    
    // The file size _should_ be an exact multiple of
    // the size of one log entry.
    if ((file_size % padded_log_entry_length) == 0)
    {
        return (file_size / padded_log_entry_length);
    }
    else
    {
        // If the file isn't an exact multiple of log entries, then assume
        // the file is corrupt and return 0.
        return 0;
    }
}

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

void Prepare_Transmit_Buffer(base64_secure_log_entry the_secure_log_entry,
                  const size_t padded_log_entry_length,
                  const size_t bytes_of_padding_required,
                  const http_endpoint endpoint, const char *log_file_name, 
                  uint8_t *Transmit_Buffer, size_t total, size_t MESSAGE_SIZE)
{
    size_t current;

    // Calculate the length of the fixed parts of the HTTP POST Header
    // const size_t FIXED_MESSAGE_SIZE =
    //     strlen(REQUEST_LINE_1) + strlen(REQUEST_LINE_3) + strlen(HEADER_1) +
    //     strlen(HEADER_2) + strlen(HEADER_3) + strlen(HEADER_4) +
    //     strlen(HEADER_5_1) + strlen(DOUBLE_CRLF);

    const size_t content_length =
        padded_log_entry_length + BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH;

    // const size_t MESSAGE_SIZE = FIXED_MESSAGE_SIZE + worst_case_data_length +
    //                             strlen(log_file_name) + content_length;

    // If user or test case has requested no HTTP echo of this log file,
    // then do nothing
    if (endpoint == HTTP_Endpoint_None)
    {
        return;
    }   

    debug_printf("Transmit_Buffer is %zu", MESSAGE_SIZE);

    // Initialize Transmit_Buffer to all 0x00 so we can dynamically calculate the
    // length of the header
    for (size_t i = 0; i < MESSAGE_SIZE; i++)
    {
        Transmit_Buffer[i] = 0x00;
    }

    snprintf((char *)Transmit_Buffer, MESSAGE_SIZE, "%s%s%s%s%s%s%s%s%zu%s",
             REQUEST_LINE_1, log_file_name, REQUEST_LINE_3, HEADER_1,
             HEADER_2, HEADER_3, HEADER_4, HEADER_5_1, content_length,
             DOUBLE_CRLF);

    // After the header has been written, we have N bytes of header,
    // occupying bytes 0 .. (N-1) of Transmit_Buffer. So.. the first byte of the
    // data block will be at index N. We can use strlen to compute
    // this since Transmit_Buffer was previously populated with all 0x00 bytes.
    size_t first_byte_of_data_index = strlen((char *)Transmit_Buffer);
    debug_printf("Length of header block is %zu", first_byte_of_data_index);

    // add the_secure_log_entry.the_entry to the Transmit_Buffer
    memcpy(&Transmit_Buffer[first_byte_of_data_index],
           &the_secure_log_entry.the_entry[0], LOG_ENTRY_LENGTH);

    // Add just the right number of spaces to make the data block,
    // spaces, hash and new_line an exact multiple of 16 bytes long.
    size_t space_index = first_byte_of_data_index + LOG_ENTRY_LENGTH;
    debug_printf("space index is %zu", space_index);
    for (size_t space_count = 0; space_count < bytes_of_padding_required;
         space_count++)
    {
        Transmit_Buffer[space_index] = space;
        space_index++;
    }

    // Add the Base64 encoded hash value from the_secure_log_entry.the_digest
    size_t hash_index = space_index;
    debug_printf("hash index is %zu", hash_index);
    memcpy(&Transmit_Buffer[hash_index], &the_secure_log_entry.the_digest[0],
           SHA256_BASE_64_DIGEST_LENGTH_BYTES);

    size_t new_line_index = hash_index + SHA256_BASE_64_DIGEST_LENGTH_BYTES;
    debug_printf("new line index is %zu", new_line_index);
    Transmit_Buffer[new_line_index] = new_line;

    // The total length of the data block, spaces, hash, new_line sequence
    // should be as expected and should be a multiple of AES_BLOCK_LENGTH_BYTES
    portable_assert((new_line_index - first_byte_of_data_index) + 1 ==
                    padded_log_entry_length);
    portable_assert(padded_log_entry_length % AES_BLOCK_LENGTH_BYTES == 0);

    // If the final byte is at offset N in Transmit_Buffer, then the current number
    // of bytes is N + 1
    current = new_line_index + 1;

    // Compute the AES_CBC_MAC of the whole block
    uint8_t binary_mac[AES_BLOCK_LENGTH_BYTES];
    aes_cbc_mac(&Transmit_Buffer[first_byte_of_data_index],
                padded_log_entry_length, &binary_mac[0]);

    // Turn that MAC into Base64 format
    uint8_t base64_mac[BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH];
    size_t olen;
    int r;
    r = mbedtls_base64_encode(&base64_mac[0],
                              BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH + 2, &olen,
                              &binary_mac[0], AES_BLOCK_LENGTH_BYTES);
    (void)r; // suppress warning on r unused.

    portable_assert(BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH == olen);

    total = current + BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH;

    // And append that MAC to the data to be sent
    memcpy(&Transmit_Buffer[current], &base64_mac[0],
           BASE_64_ENCODE_AES_CBC_MAC_DATA_LENGTH);

    debug_printf("total bytes to send is %zu", total);
    // Socket creation, init and send
    return;
  }
