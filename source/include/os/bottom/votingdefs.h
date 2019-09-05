#ifndef __VOTINGDEFS_POSIX__
#define __VOTINGDEFS_POSIX__

#include <unistd.h>
#include <assert.h>

/* The bare minimum for building the BOTTOM targets */
typedef uint32_t file_offset;
typedef uint32_t osd_file_stream;
typedef uint32_t osd_stream_buffer_handle_t;
typedef uint32_t osd_event_group_handle_t;

/* Macros */
#define osd_assert(x) assert(x)

#endif
