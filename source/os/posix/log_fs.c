#include "logging/log_fs.h"
#include "logging/debug_io.h"
#include <assert.h>

////////////////////////////////////////////
// POSIX Implementation, built on stdio.h //
////////////////////////////////////////////

Log_FS_Result Log_FS_Initialize(void)
{
    /* No action required on POSIX systems */
    return LOG_FS_OK;
}

Log_FS_Result Log_FS_Create_New(Log_Handle *stream, // OUT
                                const char *name)   // IN
{
    FILE *local_stream_ptr;

    // POSIX fopen allocates for us, unlike FreeRTOS there the caller passed in a
    // pointer to memory that it has allocated. This is rather ugly.
    local_stream_ptr = fopen(name, "a+");
    if (local_stream_ptr == NULL)
    {
        debug_printf("fopen() failed in Log_IO_Create_New\n");
        return LOG_FS_ERROR;
    }
    else
    {
        // Possibly undefined behaviour to attempt to
        // copy a FILE struct like this.
        memcpy(&stream->the_file, local_stream_ptr, sizeof(FILE));
    }

    return LOG_FS_OK;
}

Log_FS_Result Log_FS_Open(Log_Handle *stream, const char *name)
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
        // as above
        memcpy(&stream->the_file, local_stream_ptr, sizeof(FILE));
    }

    return LOG_FS_OK;
}

bool Log_FS_File_Exists(const char *name)
{
    FILE *local_stream_ptr;
    local_stream_ptr = fopen(name, "r");
    if (local_stream_ptr == NULL)
    {
        return false;
    }
    else
    {
        fclose(local_stream_ptr);
        return true;
    }
}

Log_FS_Result Log_FS_Close(Log_Handle *stream)
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

Log_FS_Result Log_FS_Sync(Log_Handle *stream)
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

/* returns number of bytes written, or 0 on failure */
size_t Log_FS_Write(Log_Handle *stream, const uint8_t *data, size_t length)
{
    return fwrite(data, 1, length, &stream->the_file);
}

/* returns number of bytes read, or 0 on failure */
size_t Log_FS_Read(Log_Handle *stream, uint8_t *data, size_t bytes_to_read)
{
    size_t result;
    result = fread(data, 1, bytes_to_read, &stream->the_file);
    if (result == bytes_to_read)
    {
        return result;
    }
    else
    {
        return 0;
    }
}

/* returns size in Bytes */
size_t Log_FS_Size(Log_Handle *stream)
{
    off_t N, position;

    position = ftell(&stream->the_file);
    fseek(&stream->the_file, 0L, SEEK_END);
    N = ftell(&stream->the_file);
    fseek(&stream->the_file, position, SEEK_SET);
    return (size_t)N;
}

/* returns value of current file pointer */
file_offset Log_FS_Tell(Log_Handle *stream)
{
    return (file_offset)ftell(&stream->the_file);
}

/* Sets current file pointer, relative to position 0
   which is the first byte of the file */
void Log_FS_Seek(Log_Handle *stream, file_offset new_offset)
{
    int dummy;
    dummy = fseek(&stream->the_file, new_offset, SEEK_SET);
}
