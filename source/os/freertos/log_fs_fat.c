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

// NOTE: not supported now
Log_FS_Result Log_FS_Create_New(Log_Handle *stream, // OUT
                                const char *name)   // IN
{
    return LOG_FS_OK;
}

// NOTE: not supported now
Log_FS_Result Log_FS_Open(Log_Handle *stream, const char *name)
{
    return LOG_FS_OK;
}

// NOTE: not supported now
bool Log_FS_File_Exists(const char *name)
{
    return false;
}

// NOTE: we close automatically
Log_FS_Result Log_FS_Close(Log_Handle *stream)
{
    return LOG_FS_OK;
}

// NOTE: we sync automatically
Log_FS_Result Log_FS_Sync(Log_Handle *stream)
{
    return LOG_FS_OK;
}

size_t Log_FS_Write(Log_Handle *stream, const uint8_t *data, size_t length)
{
    printf("Log_FS_Write: filename = %s\r\n",stream->remote_file_name);
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

// NOTE: not supported now
size_t Log_FS_Read(Log_Handle *stream, uint8_t *data, size_t bytes_to_read)
{
    return 0;
}

// NOTE: not supported now
size_t Log_FS_Size(Log_Handle *stream)
{
    return 0;
}

// NOTE: not supported now
file_offset Log_FS_Tell(Log_Handle *stream)
{
    return 0;
}

// NOTE: not supported now
void Log_FS_Seek(Log_Handle *stream, file_offset new_offset)
{
    (void)stream;
    (void)new_offset;
}
