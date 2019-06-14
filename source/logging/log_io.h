#ifndef __LOG_IO_H__
#define __LOG_IO_H__

#include "secure_log_t.h"

#ifdef TARGET_OS_FreeRTOS
#include "ff.h"

typedef FIL Log_Handle;

#else

// Assume Linux/Posix system
#include <stdio.h>
typedef FILE Log_Handle;
#endif

typedef Log_Handle *log_file;
typedef Log_Handle *log_io_stream;

// Abstract ghost state representing the overall state of the filesystem
//@ ghost int fs;


typedef enum {
	      LOG_FS_OK = 0, /* success */
	      LOG_FS_ERROR
} Log_FS_Result;


/* Mounts the FileSystem and any other initialization necessary */
/*@ assigns fs \from \nothing;
 */
Log_FS_Result Log_IO_Initialize(void);

/* Create new and empty log file. Any existing file with same name is destroyed. */
/*@ assigns fs \from fs, name;
    assigns *stream \from fs, name;
 */
Log_FS_Result Log_IO_Create_New (Log_Handle *stream, // OUT
				 const char *name);  // IN

/*@ assigns *stream \from fs, name;
 */
Log_FS_Result Log_IO_Open_Read (Log_Handle *stream, // OUT
				const char *name);  // IN

/* @ assigns fs \from fs, stream;
 */
Log_FS_Result Log_IO_Close (Log_Handle *stream); // IN

/* Forces any internal buffers out to disk. Call this after Write */
/*@ assigns fs \from fs, stream;
 */
Log_FS_Result Log_IO_Sync (Log_Handle *stream); // IN

/*@ assigns fs \from fs, stream, the_entry;
 */
Log_FS_Result Log_IO_Write_Entry (Log_Handle *stream,          // IN
                                  secure_log_entry the_entry); // IN


bool Log_IO_File_Exists (const char *name);

/* returns the number of secure_log_entry records in the given file */
size_t Log_IO_Num_Entries (Log_Handle *stream);

/* reads the n'th entry. n = 0 means the "initial" or "root" entry */
/*@
   requires n >= 0;
   requires n <  Log_IO_Num_Entries (stream);
*/
secure_log_entry Log_IO_Read_Entry (Log_Handle *stream, // IN
				    size_t n); // IN

/* reads the last entry (i.e. most recently written to the end of the file) */
secure_log_entry Log_IO_Read_Last_Entry (Log_Handle *stream);

#endif /* __LOG_IO_H__ */
