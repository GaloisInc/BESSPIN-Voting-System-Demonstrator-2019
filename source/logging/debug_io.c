#include <string.h>
#include <stdio.h>

#include "debug_io.h"
#include "log_io.h"

#ifdef DEBUG
// only declare this constant in debug mode, to avoid unused constant warnings
static const int BUFFER_SIZE = 4096; // should be large enough for any log entry
#endif // DEBUG

int debug_printf(const char *the_format, ...)
{
	#ifdef DEBUG // only do anything in debug mode
    char buffer[BUFFER_SIZE];
    
    // format the string
    
    va_list args;
    va_start(args, the_format);
    int result = vsnprintf(buffer, BUFFER_SIZE, the_format, args);
    va_end(args);
    
    if (result >= 0)
    {
      	// assuming that we successfully formatted the string,
      	// we can print it in a platform-appropriate way
      	
      	#ifdef TARGET_OS_FreeRTOS
      	FreeRTOS_debug_printf( (buffer) );
    	#else
    	fprintf(stderr, buffer);
    	#endif // TARGET_OS_FreeRTOS
    }
    #else // not in debug mode
    int result = 0;
    #endif // DEBUG
    
    return result;
}

int debug_log_printf(log_io_stream the_io_stream, const char *the_format, ...)
{
	#ifdef DEBUG // only do anything in debug mode
    char buffer[BUFFER_SIZE];
    
    // format the string
    
    va_list args;
    va_start(args, the_format);
    int result = vsnprintf(buffer, BUFFER_SIZE, the_format, args);
    va_end(args);
    
    if (result >= 0)
    {
      	// assuming that we successfully formatted the string,
      	// we can print it in a platform-appropriate way
      	
      	#ifdef TARGET_OS_FreeRTOS
      	f_printf(the_io_stream->the_file, "%8s", buffer);
      	f_flush(the_io_stream->the_file);
    	#else
    	fprintf(&the_io_stream->the_file, buffer);
    	fflush(&the_io_stream->the_file);
    	#endif // TARGET_OS_FreeRTOS
    }
    #else // not in debug mode
    int result = 0;
    #endif // DEBUG
    
    return result;
}
