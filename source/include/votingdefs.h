#ifndef __VOTINGDEFS__
#define __VOTINGDEFS__

#include <stddef.h>
#include <stdint.h>

struct voting_system_time_t {
    uint32_t year;
    uint16_t month;
    uint16_t day;
    uint16_t hour;
    uint16_t minute;
};

#if defined(VOTING_PLATFORM_POSIX)
#include "os/posix/votingdefs.h"
#elif defined(VOTING_PLATFORM_FREERTOS)
#include "os/freertos/votingdefs.h"
#else
#error "VOTING_PLATFORM is not set"
#endif

#endif
