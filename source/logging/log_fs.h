#ifndef __LOG_FS_H__
#define __LOG_FS_H__

#include <stdint.h>
#include "secure_log_t.h"

#ifdef TARGET_OS_FreeRTOS


#ifdef TARGET_FS_LittleFS

#error "TARGET_FS_LittleFS not yet implemented"

#else

// Assume Target Filesystem is FatFS

#include "ff.h"

typedef FSIZE_t file_offset;

typedef struct Log_Handles
{
    FIL the_file;
    sha256_digest previous_hash; // This should really be in secure_log
} Log_Handle;

#endif // TARGET_FS_LittleFS



#else

// !TARGET_OS_FreeRTOS so assume POSIX stdio filesystem.

#include <stdio.h>

typedef off_t file_offset;

typedef struct Log_Handles
{
    FILE the_file;
    sha256_digest previous_hash; // This should really be in secure_log
} Log_Handle;
#endif


// Abstract ghost state representing the overall state of the filesystem
//@ ghost int log_fs;


typedef enum
{
    LOG_FS_OK = 0, /* success */
    LOG_FS_ERROR
} Log_FS_Result;



// All ACSL to come - mostly copied from existing log_io.h

Log_FS_Result Log_FS_Initialize(void);

Log_FS_Result Log_FS_Create_New(Log_Handle *stream, // OUT
                                const char *name);  // IN

Log_FS_Result Log_FS_Open(Log_Handle *stream, // OUT
                          const char *name);  // IN

bool Log_FS_File_Exists(const char *name);  // IN

Log_FS_Result Log_FS_Close(Log_Handle *stream); // IN

Log_FS_Result Log_FS_Sync(Log_Handle *stream); // IN


/* returns number of bytes written, or 0 on failure */
size_t Log_FS_Write (Log_Handle *stream,
                     const uint8_t *data,
                     size_t length);

/* returns number of bytes read, or 0 on failure */
size_t Log_FS_Read (Log_Handle *stream,
                    uint8_t *data,
                    size_t bytes_to_read);

/* returns size in Bytes */
size_t Log_FS_Size(Log_Handle *stream);

/* returns value of current file pointer */
file_offset Log_FS_Tell (Log_Handle *stream);

/* Sets current file pointer, relative to position 0
   which is the first byte of the file */
void Log_FS_Seek (Log_Handle *stream,
                  file_offset new_offset);


#endif /* __LOG_FS_H__ */
