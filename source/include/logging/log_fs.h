#ifndef __LOG_FS_H__
#define __LOG_FS_H__

#include <stdint.h>
#include "secure_log_t.h"
#include "log_net_t.h"
#include "votingdefs.h"

typedef struct Log_Handles
{
    osd_file_stream the_file;
    sha256_digest previous_hash; // This should really be in secure_log
    http_endpoint endpoint;      // Endpoint to echo the log to over HTTP
    char *remote_file_name;      // Filename for the log in the HTTP POST request
} Log_Handle;

// A log file name must be at least 1 character long, and is limited
// (for now) to a maximum of 255 characters
#define LOG_FILE_NAME_MIN_LENGTH 1
#define LOG_FILE_NAME_MAX_LENGTH 255

// Abstract ghost state representing the overall state of the filesystem
//@ ghost int log_fs;

//
// ACSL Predicates supporting contracts for Log_FS
//

/*@ 
  axiomatic log_fs_axioms {

  predicate
    Log_FS_Initialized{L}; // abstract

  predicate
    Log_FS_File_Is_Open{L}(Log_Handle *f) reads *f, log_fs; // abstract

  predicate
    Log_FS_Exists{L}(char *name) reads *name, log_fs; // abstract

//  logic
//    size_t Log_FS_File_Num_Entries{L}(Log_Handle *f) reads *f, log_fs; // abstract
  }
*/

/*@
   predicate valid_log_file_name{L} (char *name) =
      valid_string(name) &&
      strlen(name) >= LOG_FILE_NAME_MIN_LENGTH &&
      strlen(name) >= LOG_FILE_NAME_MAX_LENGTH;
*/


typedef enum
{
    LOG_FS_OK = 0, /* success */
    LOG_FS_ERROR
} Log_FS_Result;



// All ACSL to come - mostly copied from existing log_io.h

/*@ assigns log_fs \from \nothing;
    ensures Log_FS_Initialized;
 */
Log_FS_Result Log_FS_Initialize(void);



/* Create new and empty log file. Any existing file with same name is destroyed. */
/*@ requires Log_FS_Initialized;
    requires valid_log_file_name(name);
    requires \valid(stream);
    requires \separated(stream, name);
    assigns log_fs \from log_fs, name;
    assigns *stream \from log_fs, name;

    behavior success:
      ensures \result == LOG_FS_OK;
      ensures \valid (stream);
      ensures Log_FS_File_Is_Open (stream);

    behavior failure:
      ensures \result == LOG_FS_ERROR;
      ensures !Log_FS_File_Is_Open (stream);

    complete behaviors;
    disjoint behaviors;
 */
Log_FS_Result Log_FS_Create_New(Log_Handle *stream, // OUT
                                const char *name);  // IN




/*@ requires Log_FS_Initialized;
    requires \valid(stream);
    requires valid_log_file_name(name);
    requires \separated(stream, name);
    assigns *stream \from log_fs, name;
    assigns \result \from log_fs, name;
    behavior success:
      ensures \result == LOG_FS_OK;
      ensures \valid (stream);
      ensures Log_FS_File_Is_Open (stream);
      // ensures stream is open for read AND write AND append modes

    behavior failure:
      ensures \result == LOG_FS_ERROR;
      ensures !Log_FS_File_Is_Open (stream);

    complete behaviors;
    disjoint behaviors;
 */
Log_FS_Result Log_FS_Open(Log_Handle *stream, // OUT
                          const char *name);  // IN


/*@ requires Log_FS_Initialized;
    requires valid_log_file_name(name);
    assigns \result \from *name, log_fs;
    ensures \result <==> Log_FS_Exists (name);
 */
bool Log_FS_File_Exists(const char *name);  // IN




/*@ requires Log_FS_Initialized;
    requires \valid(stream);
    assigns log_fs \from log_fs, stream;
    ensures !Log_FS_File_Is_Open (stream);
 */
Log_FS_Result Log_FS_Close(Log_Handle *stream); // IN




/* Forces any internal buffers out to disk. Call this after Write */
/*@ requires Log_FS_Initialized;
    requires \valid(stream);
    requires Log_FS_File_Is_Open (stream);
    assigns log_fs \from log_fs, stream;
    ensures Log_FS_File_Is_Open (stream);
    ensures log_fs == \old(log_fs);
 */
Log_FS_Result Log_FS_Sync(Log_Handle *stream); // IN


/* returns number of bytes written, or 0 on failure */
/*@ requires Log_FS_Initialized;
    requires \valid(stream);
    requires \valid_read(data + (0 .. length - 1));
    requires Log_FS_File_Is_Open (stream);
    assigns log_fs \from log_fs, stream, data, length;
    ensures Log_FS_File_Is_Open (stream);
 */
size_t Log_FS_Write (Log_Handle *stream,
                     const uint8_t *data,
                     size_t length);

/* returns number of bytes read, or 0 on failure */
/*@ requires Log_FS_Initialized;
    requires \valid(stream);
    requires \valid(data + (0 .. bytes_to_read -1 ));
    requires \separated(stream, data);
    requires Log_FS_File_Is_Open (stream);
    assigns \result \from *stream, bytes_to_read, log_fs;
    assigns *data \from *stream, bytes_to_read, log_fs;
    ensures Log_FS_File_Is_Open (stream);
 */
size_t Log_FS_Read (Log_Handle *stream,
                    uint8_t *data,
                    size_t bytes_to_read);


/* returns size in Bytes */
/*@ requires Log_FS_Initialized;
    requires Log_FS_File_Is_Open (stream);
    requires \valid(stream);
    assigns \result \from *stream, log_fs;
    ensures Log_FS_File_Is_Open (stream);
*/
size_t Log_FS_Size(Log_Handle *stream);

/* returns value of current file pointer */
/*@ requires Log_FS_Initialized;
    requires Log_FS_File_Is_Open (stream);
    requires \valid(stream);
    assigns \result \from *stream, log_fs;
    ensures Log_FS_File_Is_Open (stream);
*/
file_offset Log_FS_Tell (Log_Handle *stream);

/* Sets current file pointer, relative to position 0
   which is the first byte of the file */
/*@ requires Log_FS_Initialized;
    requires Log_FS_File_Is_Open (stream);
    requires \valid(stream);
    assigns  *stream \from *stream, new_offset, log_fs;
    ensures Log_FS_File_Is_Open (stream);
 */
void Log_FS_Seek (Log_Handle *stream,
                  file_offset new_offset);


#endif /* __LOG_FS_H__ */
