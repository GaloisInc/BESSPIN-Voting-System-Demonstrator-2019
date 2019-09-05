#ifndef __LOG_FS_FREERTOS_DEFS__H__
#define __LOG_FS_FREERTOS_DEFS__H__

#include <stdint.h>

#ifdef TARGET_FS_LittleFS

#error "TARGET_FS_LittleFS not yet implemented"

#else

// Assume Target Filesystem is FatFS

#include "ff.h"

typedef FSIZE_t file_offset;
typedef FIL     osd_file_stream;

#endif // TARGET_FS_LittleFS
#endif // __LOG_FS_FREERTOS_DEFS__H__
