#include "log_io.h"

#ifdef TARGET_OS_FreeRTOS
#error "FreeRTOS support not yet implemented"
#else

#include <string.h>

const secure_log_entry null_secure_log_entry = { {0}, {0} };

Log_FS_Result Log_IO_Initialize()
{
  /* No action required on POSIX systems */
  return LOG_FS_OK;
}


Log_FS_Result Log_IO_Create_New (Log_Handle *stream, // OUT
				 const char *name)   // IN
{
  Log_Handle *local_stream_ptr;

  printf ("w\n");

  // POSIX fopen allocates for us, unlike FreeRTOS there the caller passed in a
  // pointer to memory that it has allocated. This is rather ugly.
  local_stream_ptr = fopen (name, "a");
  if (local_stream_ptr == NULL)
    {
    printf ("x\n");
    return LOG_FS_ERROR;
    }
  else
    {
       printf ("y\n");
     
       *stream = *local_stream_ptr;
       printf ("z\n");
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

  printf ("S %zu\n", written);

  
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
