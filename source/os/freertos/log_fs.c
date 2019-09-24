#include "logging/log_fs.h"
#include "logging/debug_io.h"
#include <assert.h>

// Assume Target Filesystem is FatFS

////////////////////////////////////////////
// FreeRTOS Implementation, built on ff.h //
//                                        //
// Documentation of the ff.h filesystem   //
// is here:                               //
// www.elm-chan.org/fsw/ff/00index_e.html //
////////////////////////////////////////////

// Persistent state
FATFS FatFs; // Persistent filesystem object

Log_FS_Result Log_FS_Initialize(void)
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

Log_FS_Result Log_FS_Create_New(Log_Handle *stream, // OUT
                                const char *name)   // IN
{
    FRESULT res;

    res = f_open(&stream->the_file, name, FA_WRITE | FA_CREATE_ALWAYS);

    if (res == FR_OK)
    {
        return Log_FS_Sync(stream);
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_FS_Open(Log_Handle *stream, const char *name)
{
    FRESULT res;

    // Note we open for read/write/append so that a log file can be both
    // verified by reading back its contents, but also appended to.
    res = f_open(&stream->the_file, name, FA_READ | FA_WRITE | FA_OPEN_APPEND);

    if (res == FR_OK)
    {
        return Log_FS_Sync(stream);
    }
    else
    {
        return LOG_FS_ERROR;
    }
}

bool Log_FS_File_Exists(const char *name)
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

Log_FS_Result Log_FS_Close(Log_Handle *stream)
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

Log_FS_Result Log_FS_Sync(Log_Handle *stream)
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

size_t Log_FS_Write(Log_Handle *stream, const uint8_t *data, size_t length)
{
    FRESULT write_status;
    UINT bytes_written;

    write_status = f_write(&stream->the_file, data, length, &bytes_written);

    if ((write_status == FR_OK) && ((size_t)bytes_written == length))
    {
        Log_FS_Sync(stream); // best effort
        return length;
    }
    else
    {
        return 0;
    }
}

size_t Log_FS_Read(Log_Handle *stream, uint8_t *data, size_t bytes_to_read)
{
    FRESULT read_status;
    UINT bytes_read;
    read_status = f_read(&stream->the_file, data, bytes_to_read, &bytes_read);

    if ((read_status == FR_OK) && (bytes_to_read == bytes_read))
    {
        return bytes_to_read;
    }
    else
    {
        return 0;
    }
}

size_t Log_FS_Size(Log_Handle *stream)
{
    return (size_t)f_size(&stream->the_file);
}

file_offset Log_FS_Tell(Log_Handle *stream)
{
    return (file_offset)f_tell(&stream->the_file);
}

void Log_FS_Seek(Log_Handle *stream, file_offset new_offset)
{
    FRESULT res1;
    res1 = f_lseek(&stream->the_file, (FSIZE_t)new_offset);
    (void)res1; // suppress warning on res1 unused.
}
