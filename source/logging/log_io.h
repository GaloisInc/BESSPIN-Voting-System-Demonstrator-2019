#ifndef __LOG_IO_H__
#define __LOG_IO_H__

#include "secure_log_t.h"
#include <string.h>

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

//
// ACSL Predicates supporting contracts for Log_IO
//

/*@
  predicate
    Log_IO_Initialized{L} = \true; // abstract
  predicate
    File_Is_Open{L}(Log_Handle *f) = \true; // abstract
  predicate
    File_Exists{L}(char *name) = \true; // abstract
  logic
    size_t File_Num_Entries{L}(Log_Handle *f) = (size_t) 0; // abstract

*/


/* Mounts the FileSystem and any other initialization necessary */
/*@ assigns fs \from \nothing;
    ensures Log_IO_Initialized;
 */
Log_FS_Result Log_IO_Initialize(void);



/*@ assigns \result \from *name, fs;
    ensures \result <==> File_Exists (name);
 */
bool Log_IO_File_Exists (const char *name);



/* Create new and empty log file. Any existing file with same name is destroyed. */
/*@ requires Log_IO_Initialized;
    assigns fs \from fs, name;
    assigns *stream \from fs, name;

    behavior success:
      ensures \result == LOG_FS_OK;
      ensures \valid (stream);
      ensures File_Is_Open (stream);

    behavior failure:
      ensures \result == LOG_FS_ERROR;
      ensures !File_Is_Open (stream);
   
    complete behaviors;
    disjoint behaviors;
 */
Log_FS_Result Log_IO_Create_New (Log_Handle *stream, // OUT
				 const char *name);  // IN

/*@ requires Log_IO_Initialized;
    assigns *stream \from fs, name;
    behavior success:
      ensures \result == LOG_FS_OK;
      ensures \valid (stream);
      ensures File_Is_Open (stream);

    behavior failure:
      ensures \result == LOG_FS_ERROR;
      ensures !File_Is_Open (stream);

    complete behaviors;
    disjoint behaviors;
 */
Log_FS_Result Log_IO_Open_Read (Log_Handle *stream, // OUT
				const char *name);  // IN



/*@ requires Log_IO_Initialized;
    assigns fs \from fs, stream;
    ensures !File_Is_Open (stream);
 */
Log_FS_Result Log_IO_Close (Log_Handle *stream); // IN



/* Forces any internal buffers out to disk. Call this after Write */
/*@ requires Log_IO_Initialized;
    requires File_Is_Open (stream);
    assigns fs \from fs, stream;
    ensures File_Is_Open (stream);
 */
Log_FS_Result Log_IO_Sync (Log_Handle *stream); // IN



/*@ requires Log_IO_Initialized;
    requires File_Is_Open (stream);
    assigns fs \from fs, stream, the_entry;
 */
Log_FS_Result Log_IO_Write_Entry (Log_Handle *stream,          // IN
                                  secure_log_entry the_entry); // IN


/* returns the number of secure_log_entry records in the given file */
/*@ requires Log_IO_Initialized;
    requires File_Is_Open (stream);
    assigns \result \from *stream, fs;
    ensures \result == File_Num_Entries (stream);
 */
size_t Log_IO_Num_Entries (Log_Handle *stream);


/* reads the n'th entry. n = 0 means the "initial" or "root" entry */
// @design kiniry We need a logic query for the model of
// Log_IO_Num_Entries so that we can express the precondition for this
// function.
/*@ requires Log_IO_Initialized;
    requires File_Is_Open (stream);
    requires n >= 0;
    requires n <  File_Num_Entries (stream);
    assigns \result \from *stream, n, fs;
 */
secure_log_entry Log_IO_Read_Entry (Log_Handle *stream, // IN
				    size_t n); // IN

/* reads the last entry (i.e. most recently written to the end of the file) */
/*@ requires Log_IO_Initialized;
    requires File_Is_Open (stream);
    assigns \result \from *stream, fs;
 */
secure_log_entry Log_IO_Read_Last_Entry (Log_Handle *stream);

#endif /* __LOG_IO_H__ */
