#ifndef __VOTINGDEFS__
#define __VOTINGDEFS__

#include <stddef.h>
#include <stdint.h>

/////////////////////////////
// Common Type Definitions //
/////////////////////////////
struct voting_system_time_t {
    uint32_t year;
    uint16_t month;
    uint16_t day;
    uint16_t hour;
    uint16_t minute;
};

#if defined(VOTING_PLATFORM_BOTTOM)
#include "os/bottom/votingdefs.h"
#elif defined(VOTING_PLATFORM_POSIX)
#include "os/posix/votingdefs.h"
#elif defined(VOTING_PLATFORM_FREERTOS)
#include "os/freertos/votingdefs.h"
#else
#error "VOTING_PLATFORM is not set"
#endif

////////////////
// Simulation //
////////////////
void osd_sim_initialize(void);
void osd_sim_barcode_input(void);
void osd_sim_paper_sensor_in_pressed(void);
void osd_sim_paper_sensor_in_released(void);
void osd_sim_cast_button_pressed(void);
void osd_sim_cast_button_released(void);
void osd_sim_spoil_button_pressed(void);
void osd_sim_spoil_button_released(void);

#endif
