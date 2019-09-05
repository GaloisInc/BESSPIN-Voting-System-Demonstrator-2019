#include "logging/log_fs.h"
#include "logging/debug_io.h"
#include "votingdefs.h"
#include <assert.h>

////////////////////////////////////////////
// POSIX Implementation, built on stdio.h //
////////////////////////////////////////////

Log_FS_Result Log_FS_Initialize(void)
{
    osd_assert(0);
    return LOG_FS_OK;
}

Log_FS_Result Log_FS_Create_New(Log_Handle *stream, // OUT
                                const char *name)   // IN
{
    osd_assert(0);
    return LOG_FS_ERROR;
}

Log_FS_Result Log_FS_Open(Log_Handle *stream, const char *name)
{
    osd_assert(0);
    return LOG_FS_ERROR;
}

bool Log_FS_File_Exists(const char *name)
{
    osd_assert(0);
    return false;
}

Log_FS_Result Log_FS_Close(Log_Handle *stream)
{
    osd_assert(0);
    return LOG_FS_ERROR;
}

Log_FS_Result Log_FS_Sync(Log_Handle *stream)
{
    osd_assert(0);
    return LOG_FS_ERROR;
}

/* returns number of bytes written, or 0 on failure */
size_t Log_FS_Write(Log_Handle *stream, const uint8_t *data, size_t length)
{
    osd_assert(0);
    return 0;
}

/* returns number of bytes read, or 0 on failure */
size_t Log_FS_Read(Log_Handle *stream, uint8_t *data, size_t bytes_to_read)
{
    osd_assert(0);
    return 0;
}

/* returns size in Bytes */
size_t Log_FS_Size(Log_Handle *stream)
{
    osd_assert(0);
    return 0;
}

/* returns value of current file pointer */
file_offset Log_FS_Tell(Log_Handle *stream)
{
    osd_assert(0);
    return 0;
}

/* Sets current file pointer, relative to position 0
   which is the first byte of the file */
void Log_FS_Seek(Log_Handle *stream, file_offset new_offset)
{
    osd_assert(0);
}
