#ifndef __VOTINGDEFS__
#define __VOTINGDEFS__

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

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

// @spec abakst Specifications needed for for hardware, related to the
// above I think we probably want some ghost `uint8_t` array to model
// these reads/writes.
extern uint8_t gpio_mem[8];

// @todo kiniry This is a placeholder state representation so that we
// can talk about the state of memory-mapped firmware.  It should
// probably be refined to a separate memory-mapped region (or more
// than one) per device and an invariant should stipulate that the
// memory regions are distinct.
typedef bool firmware_state;
extern firmware_state the_firmware_state;

#if defined(VOTING_PLATFORM_BOTTOM)
#include "os/bottom/votingdefs.h"
#elif defined(VOTING_PLATFORM_POSIX)
#include "os/posix/votingdefs.h"
#elif defined(VOTING_PLATFORM_FREERTOS)
#include "os/freertos/votingdefs_freertos.h"
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
