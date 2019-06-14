#include "log_io.h"

// Local constants
const secure_log_entry null_secure_log_entry = { {0}, {0} };
const size_t size_of_one_log_entry = LOG_ENTRY_LENGTH + SHA256_DIGEST_LENGTH_BYTES;

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
  res = f_mount (&FatFs,
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

Log_FS_Result Log_IO_Create_New (Log_Handle *stream, // OUT
				 const char *name)   // IN
{
  FRESULT res;
  res = f_open(stream, name, FA_WRITE | FA_CREATE_ALWAYS);

  if (res == FR_OK)
    {
      return LOG_FS_OK;
    }
  else
    {
      return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Open_Read (Log_Handle *stream, // OUT
				const char *name)   // IN
{
  FRESULT res;
  res = f_open(stream, name, FA_READ | FA_OPEN_EXISTING);

  if (res == FR_OK)
    {
      return LOG_FS_OK;
    }
  else
    {
      return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Close (Log_Handle *stream) // IN
{
  FRESULT res;
  res = f_close (stream);
  if (res == FR_OK)
    {
      return LOG_FS_OK;
    }
  else
    {
      return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Sync (Log_Handle *stream)  // IN
{
  FRESULT res;
  res = f_sync (stream);
  if (res == FR_OK)
    {
      return LOG_FS_OK;
    }
  else
    {
      return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Write_Entry (Log_Handle *stream,          // IN
                                  secure_log_entry the_entry) // IN
{
  FRESULT res1, res2;
  UINT bytes_written1, bytes_written2;
  res1 = f_write (stream, &the_entry.the_entry[0], LOG_ENTRY_LENGTH, &bytes_written1);
  res2 = f_write (stream, &the_entry.the_digest[0], SHA256_DIGEST_LENGTH_BYTES, &bytes_written2);

  if (res1 == FR_OK &&
      res2 == FR_OK &&
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

bool Log_IO_File_Exists (const char *name)
{
  Log_Handle file;
  FRESULT res;
  res = f_open(&file, name, FA_READ | FA_OPEN_EXISTING);

  if (res == FR_OK)
    {
      res = f_close (&file);
      return true;
    }
  else
    {
      return false;
    }
}


size_t Log_IO_Num_Entries (Log_Handle *stream)
{
  size_t file_size;

  file_size = (size_t) f_size (stream);
  
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

secure_log_entry Log_IO_Read_Entry (Log_Handle *stream, // IN
				    size_t n)  // IN
{
  FRESULT res1;  
  FSIZE_t original_offset;
  size_t byte_offset_of_entry_n;  

  // Entry 0 is at byte offset 0, so...
  byte_offset_of_entry_n = n * size_of_one_log_entry;

  // Record the current offset so we can restore it later...
  original_offset = f_tell (stream);

  res1 = f_lseek (stream, (FSIZE_t) byte_offset_of_entry_n);
  if (res1 == FR_OK)
    {
      secure_log_entry result;
      FRESULT res2, res3, res4;  
      UINT bytes_read1, bytes_read2;

      // read the data
      res2 = f_read (stream, &result.the_entry[0], LOG_ENTRY_LENGTH, &bytes_read1);
      res3 = f_read (stream, &result.the_digest[0], SHA256_DIGEST_LENGTH_BYTES, &bytes_read2);

      // Restore the original offset
      res4 = f_lseek (stream, original_offset);
      if (res2 == FR_OK &&
          res3 == FR_OK &&
          res4 == FR_OK &&
          bytes_read1 == LOG_ENTRY_LENGTH &&
          bytes_read2 == SHA256_DIGEST_LENGTH_BYTES)
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

secure_log_entry Log_IO_Read_Last_Entry (Log_Handle *stream)
{
  // If a log has N log entries, they are numbered 0 .. (N - 1), so
  // we need to ask for the (N - 1)'th

  size_t N;
  N = Log_IO_Num_Entries (stream);
  
  // We cannot get anything from an empty file so
  if (N > 0)
    {
      return Log_IO_Read_Entry (stream, N - 1);
    }
  else
    {
      return null_secure_log_entry;
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


Log_FS_Result Log_IO_Create_New (Log_Handle *stream, // OUT
				 const char *name)   // IN
{
  Log_Handle *local_stream_ptr;

  // POSIX fopen allocates for us, unlike FreeRTOS there the caller passed in a
  // pointer to memory that it has allocated. This is rather ugly.
  local_stream_ptr = fopen (name, "w");
  if (local_stream_ptr == NULL)
    {
      printf ("fopen() failed\n");
      return LOG_FS_ERROR;
    }
  else
    {
      printf ("sizeof(FILE) is %lu\n", sizeof(FILE));
      
      // RCC - this is dodgy - possibly undefined behaviour to attempt to
      // copy a FILE struct like this.  

      printf ("Copying the FILE structure\n");
      memcpy (stream, local_stream_ptr, sizeof(FILE));
      printf ("Done copying\n");
    }
  
  return LOG_FS_OK;
}

Log_FS_Result Log_IO_Open_Read (Log_Handle *stream, // OUT
				const char *name)   // IN
{
  return LOG_FS_ERROR;
}

Log_FS_Result Log_IO_Close (Log_Handle *stream) // IN
{
  if (fclose (stream) == 0)
    {
      return LOG_FS_OK;
    }
  else
    {
      return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Sync (Log_Handle *stream)  // IN
{
  if (fflush (stream) == 0)
    {
      return LOG_FS_OK;
    }
  else
    {
      return LOG_FS_ERROR;
    }
}

Log_FS_Result Log_IO_Write_Entry (Log_Handle *stream,          // IN
                                  secure_log_entry the_entry) // IN
{
  size_t written;

  printf ("Going for the first write\n");
  written = fwrite (&the_entry.the_entry[0], 1, LOG_ENTRY_LENGTH, stream);
  printf ("Goinf for the second write\n");
  written += fwrite (&the_entry.the_digest[0], 1, SHA256_DIGEST_LENGTH_BYTES, stream);

  printf ("Bytes written is %zu\n", written);

  if (written == (LOG_ENTRY_LENGTH + SHA256_DIGEST_LENGTH_BYTES))
    {
      return LOG_FS_OK;
    }
  else
    {
      return LOG_FS_ERROR;
    }
}


bool Log_IO_File_Exists (const char *name)
{
  return false;
}


size_t Log_IO_Num_Entries (Log_Handle *stream)
{
  return 0;
}

secure_log_entry Log_IO_Read_Entry (Log_Handle *stream, // IN
				    size_t n)  // IN
{
  return null_secure_log_entry;
}

secure_log_entry Log_IO_Read_Last_Entry (Log_Handle *stream)
{
  return null_secure_log_entry;
}
#endif
