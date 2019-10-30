#include <FreeRTOS.h>
#include <FreeRTOSConfig.h>

#include <string.h>

#include "logging/debug_io.h"
#include "logging/log_io.h"
#include "logging/log_fs.h"

#ifdef VOTING_SYSTEM_DEBUG
// only declare this constant in debug mode, to avoid unused constant warnings
static const int BUFFER_SIZE = 4096; // should be large enough for any log entry
#endif // VOTING_SYSTEM_DEBUG

int debug_printf(const char *the_format, ...)
{
    #ifdef VOTING_SYSTEM_DEBUG // only do anything in debug mode
    #pragma message "Using VOTING_SYSTEM_DEBUG option"
    char buffer[BUFFER_SIZE];
    
    // format the string
    
    va_list args;
    va_start(args, the_format);
    int result = vsnprintf(buffer, BUFFER_SIZE, the_format, args);
    va_end(args);
    
    if (result >= BUFFER_SIZE - 2) {
        // the buffer was overrun or almost filled, so replace 
        // the last three characters with a CR/LF and a null terminator
        buffer[BUFFER_SIZE - 3] = '\r';
        buffer[BUFFER_SIZE - 2] = '\n';
        buffer[BUFFER_SIZE - 1] = 0;
    } else {
        // the buffer was not overrun, so find the null terminator and
        // insert a CR/LF
        int len = strlen(buffer);
        buffer[len] = '\r';
        buffer[len + 1] = '\n';
        buffer[len + 2] = 0;
    }
    
    if (result >= 0)
    {
        // assuming that we successfully formatted the string,
        // we can print it in a platform-appropriate way
        printf("%lu.%lu[s]: %s", uptimeMs()/1000, uptimeMs(), buffer);
    }
    #else // not in debug mode
    int result = 0;
    #endif // VOTING_SYSTEM_DEBUG
    
    return result;
}

int debug_log_printf(log_io_stream the_io_stream, const char *the_format, ...)
{
    #if defined (VOTING_SYSTEM_DEBUG) && defined (FS_LOGS) // only do anything in debug mode and if a file system is present
    char buffer[BUFFER_SIZE];
    
    // format the string
    va_list args;
    va_start(args, the_format);
    int result = vsnprintf(buffer, BUFFER_SIZE, the_format, args);
    va_end(args);
    
    if (result >= BUFFER_SIZE - 2) {
        // the buffer was overrun or almost filled, so replace 
        // the last three characters with a CR/LF and a null terminator
        buffer[BUFFER_SIZE - 3] = '\r';
        buffer[BUFFER_SIZE - 2] = '\n';
        buffer[BUFFER_SIZE - 1] = 0;
    } else {
        // the buffer was not overrun, so find the null terminator and
        // insert a CR/LF
        int len = strlen(buffer);
        buffer[len] = '\r';
        buffer[len + 1] = '\n';
        buffer[len + 2] = 0;
    }
    
    if (result >= 0)
    {
        // assuming that we successfully formatted the string,
        // we can print it in a platform-appropriate way
        printf("Calling debug IO\r\n");
        Log_FS_Write(the_io_stream, (uint8_t*)buffer, strlen(buffer));
        Log_FS_Sync(the_io_stream);
        
    }
    #else // not in debug mode
    (void)the_io_stream;
    (void)the_format;
    int result = 0;
    #endif // VOTING_SYSTEM_DEBUG
    
    return result;
}
