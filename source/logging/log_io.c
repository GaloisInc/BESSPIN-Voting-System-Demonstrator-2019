#include "log_io.h"
#include "debug_io.h"
#include <assert.h>

// Local constants
const secure_log_entry null_secure_log_entry = {{0}, {0}};
const size_t size_of_one_log_entry =
    LOG_ENTRY_LENGTH + SHA256_DIGEST_LENGTH_BYTES;

const base64_secure_log_entry null_base64_secure_log_entry = {{0}, {0}};
const size_t size_of_one_base64_block_log_entry =
    BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;

static const char space = ' ';
static const char new_line = '\n';

#ifdef TARGET_OS_FreeRTOS

////////////////////////////////////////////
// FreeRTOS Implementation, built on ff.h //
//                                        //
// Documentation of the ff.h filesystem   //
// is here:                               //
// www.elm-chan.org/fsw/ff/00index_e.html //
////////////////////////////////////////////

// Persistent state
FATFS FatFs; // Persistent filesystem object

Log_FS_Result Log_IO_Initialize()
{
    FRESULT res;
    res = f_mount(&FatFs,
                  "", // Mount the default volume
                  0); // Mount on first access

    if (res == FR_OK)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Create_New(Log_Handle *stream, // OUT
                                const char *name)   // IN
{
    FRESULT res;

    res = f_open(&stream->the_file, name, FA_WRITE | FA_CREATE_ALWAYS);

    if (res == FR_OK)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Open(Log_Handle *stream, // OUT
                          const char *name)   // IN
{
    FRESULT res;

    // Note we open for read/write/append so that a log file can be both
    // verified by reading back its contents, but also appended to.
    res = f_open(&stream->the_file, name, FA_READ | FA_WRITE | FA_OPEN_APPEND);

    if (res == FR_OK)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Close(Log_Handle *stream) // IN
{
    FRESULT res;
    res = f_close(&stream->the_file);
    if (res == FR_OK)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Sync(Log_Handle *stream) // IN
{
    FRESULT res;
    res = f_sync(&stream->the_file);
    if (res == FR_OK)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Write_Entry(Log_Handle *stream,         // IN
                                 secure_log_entry the_entry) // IN
{
    FRESULT res1, res2;
    UINT bytes_written1, bytes_written2;
    res1 = f_write(&stream->the_file, &the_entry.the_entry[0], LOG_ENTRY_LENGTH,
                   &bytes_written1);
    res2 = f_write(&stream->the_file, &the_entry.the_digest[0],
                   SHA256_DIGEST_LENGTH_BYTES, &bytes_written2);

    if (res1 == FR_OK && res2 == FR_OK && bytes_written1 == LOG_ENTRY_LENGTH &&
        bytes_written2 == SHA256_DIGEST_LENGTH_BYTES)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

bool Log_IO_File_Exists(const char *name)
{
    FIL file;
    FRESULT res;
    res = f_open(&file, name, FA_READ | FA_OPEN_EXISTING);

    if (res == FR_OK)
    {
        res = f_close(&file);
        return true;
    }
    else
    {
        return false;
    }
}

size_t Log_IO_Num_Entries(Log_Handle *stream)
{
    size_t file_size;

    file_size = (size_t)f_size(&stream->the_file);

    // The file size _should_ be an exact multiple of
    // the size of one log entry.
    if ((file_size % size_of_one_log_entry) == 0)
    {
        return (file_size / size_of_one_log_entry);
    }
    else
    {
        // If the file isn't an exact multiple of log entries, then assume
        // the file is corrupt and return 0.
        return 0;
    }
}

secure_log_entry Log_IO_Read_Entry(Log_Handle *stream, // IN
                                   size_t n)           // IN
{
    FRESULT res1;
    FSIZE_t original_offset;
    size_t byte_offset_of_entry_n;

    // Entry 0 is at byte offset 0, so...
    byte_offset_of_entry_n = n * size_of_one_log_entry;

    // Record the current offset so we can restore it later...
    original_offset = f_tell(&stream->the_file);

    res1 = f_lseek(&stream->the_file, (FSIZE_t)byte_offset_of_entry_n);
    if (res1 == FR_OK)
    {
        secure_log_entry result;
        FRESULT read_log_entry_status, read_digest_status,
            restore_offset_status;
        UINT bytes_log_entry, bytes_sha_digest;

        // read the data
        read_log_entry_status = f_read(&stream->the_file, &result.the_entry[0],
                                       LOG_ENTRY_LENGTH, &bytes_log_entry);
        read_digest_status =
            f_read(&stream->the_file, &result.the_digest[0],
                   SHA256_DIGEST_LENGTH_BYTES, &bytes_sha_digest);

        // Restore the original offset
        restore_offset_status = f_lseek(&stream->the_file, original_offset);
        if (read_log_entry_status == FR_OK && read_digest_status == FR_OK &&
            restore_offset_status == FR_OK &&
            bytes_log_entry == LOG_ENTRY_LENGTH &&
            bytes_sha_digest == SHA256_DIGEST_LENGTH_BYTES)
        {
            return result;
        }
        else
        {
            return null_secure_log_entry;
        }
    }
    else
    {
        return null_secure_log_entry;
    }
}

secure_log_entry Log_IO_Read_Last_Entry(Log_Handle *stream)
{
    // If a log has N log entries, they are numbered 0 .. (N - 1), so
    // we need to ask for the (N - 1)'th

    size_t N;
    N = Log_IO_Num_Entries(stream);

    // We cannot get anything from an empty file so
    if (N > 0)
    {
        return Log_IO_Read_Entry(stream, N - 1);
    }
    else
    {
        return null_secure_log_entry;
    }
}
/*dragan added*/
size_t Log_IO_Num_Base64_Entries(Log_Handle *stream)
{
    size_t file_size;

    file_size = (size_t)f_size(&stream->the_file);

    // The file size _should_ be an exact multiple of
    // the size of one log entry.
    if ((file_size % size_of_one_base64_block_log_entry) == 0)
    {
        return (file_size / size_of_one_base64_block_log_entry);
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
    // If a log has N log entries, they are numbered 0 .. (N - 1), so
    // we need to ask for the (N - 1)'th

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

secure_log_entry Log_IO_Read_Base64_Entry(Log_Handle *stream, // IN
                                          size_t n)           // IN
{
    FRESULT res1;
    FSIZE_t original_offset;
    size_t byte_offset_of_entry_n;
    char dummy_char;
    secure_log_entry secure_log_entry_result;
    size_t olen;
    int r;

    // Entry 0 is at byte offset 0, so...
    byte_offset_of_entry_n = n * size_of_one_base64_block_log_entry;

    // Record the current offset so we can restore it later...
    original_offset = f_tell(&stream->the_file);

    res1 = f_lseek(&stream->the_file, (FSIZE_t)byte_offset_of_entry_n);
    if (res1 == FR_OK)
    {
        base64_secure_log_entry result;
        FRESULT read_log_entry_status, read_space_status, read_digest_status,
            read_new_line_char_status, restore_offset_status;
        UINT bytes_log_entry, bytes_sha_digest, space_length,
            new_line_char_length;

        // read the data
        read_log_entry_status = f_read(&stream->the_file, &result.the_entry[0],
                                       LOG_ENTRY_LENGTH, &bytes_log_entry);

        read_space_status =
            f_read(&stream->the_file, &dummy_char, 1, &space_length);

        read_digest_status =
            f_read(&stream->the_file, &result.the_digest[0],
                   SHA256_BASE_64_DIGEST_LENGTH_BYTES, &bytes_sha_digest);

        read_new_line_char_status = f_read(&stream->the_file, &dummy_char,
                                           1, &new_line_char_length);

        // Restore the original offset
        restore_offset_status = f_lseek(&stream->the_file, original_offset);
        if (read_log_entry_status == FR_OK && read_digest_status == FR_OK &&
            restore_offset_status == FR_OK &&
            bytes_log_entry == LOG_ENTRY_LENGTH &&
            bytes_sha_digest == SHA256_BASE_64_DIGEST_LENGTH_BYTES &&
            space_length == 1 && new_line_char_length == 1)
        {
            // decode, create secure log entry  and return
            r = mbedtls_base64_decode(&secure_log_entry_result.the_digest[0],
                                      SHA256_DIGEST_LENGTH_BYTES + 1, &olen,
                                      &result.the_digest[0],
                                      SHA256_BASE_64_DIGEST_LENGTH_BYTES);

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
        else
        {
            return null_secure_log_entry;
        }
    }
    else
    {
        return null_secure_log_entry;
    }
}

Log_FS_Result Log_IO_Write_Base64_Entry(Log_Handle *stream,                // IN
                                        secure_log_entry the_entry) // IN
{
    size_t olen;
    int r;
    FRESULT write_entry_status, write_digest_status;
    base64_secure_log_entry base_64_current_entry;
    r = mbedtls_base64_encode(&base_64_current_entry.the_digest[0],
                              SHA256_BASE_64_DIGEST_LENGTH_BYTES + 2, &olen,
                              &the_entry.the_digest[0],
                              SHA256_DIGEST_LENGTH_BYTES);
    assert(SHA256_BASE_64_DIGEST_LENGTH_BYTES == olen);
    
    memcpy (&base_64_current_entry.the_entry[0], &the_entry.the_entry[0],
                    LOG_ENTRY_LENGTH);

    UINT bytes_written1, bytes_written2, space_written, new_line_char_written;
    write_entry_status = f_write(&stream->the_file, &base_64_current_entry.the_entry[0],
                                 LOG_ENTRY_LENGTH, &bytes_written1);

    space_written = f_putc(space, &stream->the_file);

    write_digest_status = f_write(&stream->the_file, &base_64_current_entry.the_digest[0],
                                  SHA256_DIGEST_LENGTH_BYTES, &bytes_written2);

    new_line_char_written = f_putc(new_line, &stream->the_file);

    if (write_entry_status == FR_OK && write_digest_status == FR_OK &&
        space_written == 1 && new_line_char_written == 1 &&
        bytes_written1 == LOG_ENTRY_LENGTH &&
        bytes_written2 == SHA256_DIGEST_LENGTH_BYTES)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}
#else

////////////////////////////////////////////
// POSIX Implementation, built on stdio.h //
////////////////////////////////////////////

#include <string.h>

Log_FS_Result Log_IO_Initialize()
{
    /* No action required on POSIX systems */
    return LOG_FS_OK;
}

Log_FS_Result Log_IO_Create_New(Log_Handle *stream, // OUT
                                const char *name)   // IN
{
    FILE *local_stream_ptr;

    // POSIX fopen allocates for us, unlike FreeRTOS there the caller passed in a
    // pointer to memory that it has allocated. This is rather ugly.
    local_stream_ptr = fopen(name, "w");
    if (local_stream_ptr == NULL)
    {
        debug_printf("fopen() failed in Log_IO_Create_New\n");
        return LOG_FS_ERROR;
    }
    else
    {
        // RCC - this is dodgy - possibly undefined behaviour to attempt to
        // copy a FILE struct like this.
        memcpy(&stream->the_file, local_stream_ptr, sizeof(FILE));
    }

    return LOG_FS_OK;
}

Log_FS_Result Log_IO_Open(Log_Handle *stream, // OUT
                          const char *name)   // IN
{
    FILE *local_stream_ptr;

    // POSIX fopen allocates for us, unlike FreeRTOS there the caller passed in a
    // pointer to memory that it has allocated. This is rather ugly.
    // Note we open for read/write/append so that a log file can be both
    // verified by reading back its contents, but also appended to.
    local_stream_ptr = fopen(name, "a+");
    if (local_stream_ptr == NULL)
    {
        debug_printf("fopen() failed in Log_IO_Open\n");
        return LOG_FS_ERROR;
    }
    else
    {
        // RCC - as above
        memcpy(&stream->the_file, local_stream_ptr, sizeof(FILE));
    }

    return LOG_FS_OK;
}

Log_FS_Result Log_IO_Close(Log_Handle *stream) // IN
{
    if (fclose(&stream->the_file) == 0)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Sync(Log_Handle *stream) // IN
{
    if (fflush(&stream->the_file) == 0)
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Write_Entry(Log_Handle *stream,         // IN
                                 secure_log_entry the_entry) // IN
{
    size_t written;

    written =
        fwrite(&the_entry.the_entry[0], 1, LOG_ENTRY_LENGTH, &stream->the_file);
    written += fwrite(&the_entry.the_digest[0], 1, SHA256_DIGEST_LENGTH_BYTES,
                      &stream->the_file);

    if (written == (LOG_ENTRY_LENGTH + SHA256_DIGEST_LENGTH_BYTES))
    {
        return LOG_FS_OK;
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

bool Log_IO_File_Exists(const char *name)
{
    FILE *local_stream_ptr;
    local_stream_ptr = fopen(name, "r");
    if (local_stream_ptr == NULL)
    {
        return false;
    }
    fclose(local_stream_ptr);
    return true;
}

size_t Log_IO_Num_Entries(Log_Handle *stream)
{
    off_t position = ftell(&stream->the_file);
    fseek(&stream->the_file, 0L, SEEK_END);
    off_t N = ftell(&stream->the_file) / SECURE_LOG_ENTRY_LENGTH;
    fseek(&stream->the_file, position, SEEK_SET);
    return N;
}

secure_log_entry Log_IO_Read_Entry(Log_Handle *stream, // IN
                                   size_t n)           // IN
{
    fseek(&stream->the_file, 0, SEEK_SET);
    off_t original_offset;
    off_t byte_offset_of_entry_n;
    byte_offset_of_entry_n = n * size_of_one_log_entry;
    original_offset = ftell(&stream->the_file);
    fseek(&stream->the_file, byte_offset_of_entry_n, SEEK_CUR);
    secure_log_entry result;
    size_t ret_entry =
        fread(&result.the_entry[0], 1, LOG_ENTRY_LENGTH, &stream->the_file);
    size_t ret_digest = fread(&result.the_digest[0], 1,
                              SHA256_DIGEST_LENGTH_BYTES, &stream->the_file);

    // Restore the original offset
    fseek(&stream->the_file, original_offset, SEEK_SET);
    if (ret_entry == LOG_ENTRY_LENGTH &&
        ret_digest == SHA256_DIGEST_LENGTH_BYTES)
    {
        return result;
    }
    return null_secure_log_entry;
}

secure_log_entry Log_IO_Read_Last_Entry(Log_Handle *stream)
{
    size_t N;
    N = Log_IO_Num_Entries(stream);

    // We cannot get anything from an empty file so
    if (N > 0)
    {
        return Log_IO_Read_Entry(stream, N - 1);
    }
    else
    {
        return null_secure_log_entry;
    }
}

Log_FS_Result Log_IO_Write_Base64_Entry(Log_Handle *stream,
                                        secure_log_entry the_entry)
{
    size_t olen;
    int r;
    size_t written;
    base64_secure_log_entry base_64_current_entry;
    r = mbedtls_base64_encode(&base_64_current_entry.the_digest[0],
                              SHA256_BASE_64_DIGEST_LENGTH_BYTES + 2, &olen,
                              &the_entry.the_digest[0],
                              SHA256_DIGEST_LENGTH_BYTES);
    assert(SHA256_BASE_64_DIGEST_LENGTH_BYTES == olen);
    memcpy (&base_64_current_entry.the_entry[0], &the_entry.the_entry[0],
                    LOG_ENTRY_LENGTH);

    written =
        fwrite(&base_64_current_entry.the_entry[0], 1, LOG_ENTRY_LENGTH, &stream->the_file);

    fputc(space, &stream->the_file);
    written++;

    written += fwrite(&base_64_current_entry.the_digest[0], 1,
                      SHA256_BASE_64_DIGEST_LENGTH_BYTES, &stream->the_file);

    fputc(new_line, &stream->the_file);
    written++;

    if (written == (BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH))
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
    char dummy_char;
    size_t olen;
    int r;

    fseek(&stream->the_file, 0, SEEK_SET);
    off_t original_offset;
    off_t byte_offset_of_entry_n;
    byte_offset_of_entry_n = n * size_of_one_base64_block_log_entry;
    original_offset = ftell(&stream->the_file);
    fseek(&stream->the_file, byte_offset_of_entry_n, SEEK_CUR);

    base64_secure_log_entry result;

    size_t ret_entry =
        fread(&result.the_entry[0], 1, LOG_ENTRY_LENGTH, &stream->the_file);

    size_t ret_space = fread(&dummy_char, 1, 1, &stream->the_file);

    size_t ret_digest =
        fread(&result.the_digest[0], 1, SHA256_BASE_64_DIGEST_LENGTH_BYTES,
              &stream->the_file);

    size_t ret_new_line = fread(&dummy_char, 1, 1, &stream->the_file);

    // Restore the original offset
    fseek(&stream->the_file, original_offset, SEEK_SET);

    if (ret_entry == LOG_ENTRY_LENGTH &&
        ret_digest == SHA256_BASE_64_DIGEST_LENGTH_BYTES && ret_space == 1 &&
        ret_new_line == 1)
    {
        // decode, create secure_log_entry and return
        r = mbedtls_base64_decode(&secure_log_entry_result.the_digest[0],
                                  SHA256_DIGEST_LENGTH_BYTES + 1, &olen,
                                  &result.the_digest[0],
                                  SHA256_BASE_64_DIGEST_LENGTH_BYTES);

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
    off_t position = ftell(&stream->the_file);
    fseek(&stream->the_file, 0L, SEEK_END);
    off_t N = ftell(&stream->the_file) / BASE64_SECURE_BLOCK_LOG_ENTRY_LENGTH;
    fseek(&stream->the_file, position, SEEK_SET);
    return N;
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

#endif
