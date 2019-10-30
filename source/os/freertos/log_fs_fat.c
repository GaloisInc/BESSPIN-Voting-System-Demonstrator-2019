#include "logging/log_fs.h"
#include "logging/debug_io.h"
#include <assert.h>

Log_FS_Result Log_FS_Initialize(void)
{
    if (sdlib_initialize()) {
        return LOG_FS_OK;
    } else {
        return LOG_FS_ERROR;
    }
}

// NOTE: new files are created automatically upon opening
Log_FS_Result Log_FS_Create_New(Log_Handle *stream, // OUT
                                const char *name)   // IN
{
    (void)stream;
    (void)name;
    return LOG_FS_OK;
}

// NOTE: opening is automatic
Log_FS_Result Log_FS_Open(Log_Handle *stream, const char *name)
{
    return LOG_FS_OK;
}

// NOTE: not supported now
bool Log_FS_File_Exists(const char *name)
{
    return sdlib_exists(name);
}

Log_FS_Result Log_FS_Close(Log_Handle *stream)
{
    sdlib_close(stream->remote_file_name);
    return LOG_FS_OK;
}

// NOTE: we sync automatically and also upon closing the file
Log_FS_Result Log_FS_Sync(Log_Handle *stream)
{
    sdlib_sync(stream->remote_file_name);
    return LOG_FS_OK;
}

size_t Log_FS_Write(Log_Handle *stream, const uint8_t *data, size_t length)
{
    size_t r = sdlib_write_to_file(stream->remote_file_name, data, length);

    if (r == length)
    {
        return r;
    }
    else
    {
        return 0;
    }
}

size_t Log_FS_Read(Log_Handle *stream, uint8_t *data, size_t bytes_to_read)
{
    size_t r = sdlib_read_from_file(stream->remote_file_name, data, bytes_to_read);
    return r;
}

size_t Log_FS_Size(Log_Handle *stream)
{
    return sdlib_size(stream->remote_file_name);
}

// NOTE: not supported now
file_offset Log_FS_Tell(Log_Handle *stream)
{
    return sdlib_tell(stream->remote_file_name);
}

// NOTE: not supported now
void Log_FS_Seek(Log_Handle *stream, file_offset new_offset)
{
    sdlib_seek(stream->remote_file_name, new_offset);
}
