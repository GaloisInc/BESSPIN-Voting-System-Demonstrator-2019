#ifndef __LOG_FS_FREERTOS_DEFS__H__
#define __LOG_FS_FREERTOS_DEFS__H__

#include <stdint.h>


#if TARGET_FS_FAT
#include "SDLib.h"
typedef uint32_t    file_offset;
typedef char*     osd_file_stream;
#elif TARGET_FS_BLACK_SESAME
#error "TARGET_FS_LittleFS not yet implemented"
#else
// Provide dummy types
typedef size_t    file_offset;
typedef char*     osd_file_stream;
#endif
#endif // __LOG_FS_FREERTOS_DEFS__H__
