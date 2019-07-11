#include "log_io.h"
#include "debug_io.h"
#include "log_fs.h"
#include "log_net.h"
#include <assert.h>
#include <string.h>

// Local constants
const secure_log_entry null_secure_log_entry = {{0}, {0}};



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

    // Step 1 - Form the Base64 encoding of the hash
    r = mbedtls_base64_encode(&base_64_current_entry.the_digest[0],
                              SHA256_BASE_64_DIGEST_LENGTH_BYTES + 2, &olen,
                              &the_entry.the_digest[0],
                              SHA256_DIGEST_LENGTH_BYTES);
    (void)r; // suppress warning on r unused.
    assert(SHA256_BASE_64_DIGEST_LENGTH_BYTES == olen);

    // Step 2 - Copy the data block
    memcpy(&base_64_current_entry.the_entry[0], &the_entry.the_entry[0],
           LOG_ENTRY_LENGTH);

    // Step 3 - Write (data # spaces # base64_hash # new_line) to file
    written = Log_FS_Write(stream, &base_64_current_entry.the_entry[0],
                           LOG_ENTRY_LENGTH);

    // Write just to right number of spaces, as computed above
    written += Log_FS_Write(stream, spaces, bytes_of_padding_required);

    written += Log_FS_Write(stream, &base_64_current_entry.the_digest[0],
                            SHA256_BASE_64_DIGEST_LENGTH_BYTES);
    written += Log_FS_Write(stream, &new_line, 1);

    // Step 4 - Write same data over network to the Reporting System
    Log_Net_Send (base_64_current_entry,
                  padded_log_entry_length,
                  bytes_of_padding_required,
                  stream->endpoint,
                  stream->remote_file_name);

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
