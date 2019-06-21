/**
 * Smart Ballot Logging API
 * @refine log.lando
 */
#ifndef __SYSTEM_LOG__
#define __SYSTEM_LOG__

// General includes

// Subsystem includes
#include "secure_system_log_t.h"

// Per system requirements, even system event that causes a system
// state change must be logged to this secure log.  In voting systems
// vernacular, relevant state changes are those relevant to overall
// system state (i.e., not microarchitectural state or state changes
// internal to device drivers, firmware, etc.).

// @design kiniry C enumerations are integers, so on the SBB we would
// be using 32 bits to encode the system event type in memory. When
// we serialize this to the system log, we will write the value in
// ASCII, and probably limit it to two characters for the moment.
typedef enum
{
    power_on,
    firmware_initialization,
    device_driver_initialization,
    standby,
    motor_forward,
    motor_stop,
    motor_backward,
    paper_detected,
    paper_inserted,
    paper_accepted,
    paper_returned,
    early_paper_sensor_enabled,
    late_paper_sensor_enabled,
    early_paper_sensor_disabled,
    late_paper_sensor_disabled,
    display_text,
    cast_button_pressed,
    cast_button_released,
    spoil_button_pressed,
    spoil_button_released,
    cast_light_on,
    cast_light_off,
    spoil_light_on,
    spoil_light_off
} system_log_event;

// @todo kiniry We need this kind of data invariant.
// global invariant system_log_entries_are_all_the_same_size:
//   forall e in system_log_event;
//     sizeof(voting_system_secure_system_log_entries) == 256;

typedef struct voting_system_secure_system_log_entries
{
    uint32_t time;          // 4 bytes, thus 4 of 256 bytes available
    system_log_event event; // 4 bytes, thus 8 of 256 bytes available
    char *message;          // 248 bytes available
} voting_system_secure_system_log_entry;

/*@ requires \valid(ascii_encoded_entry + (0..255));
  @ assigns ascii_encoded_entry + (0..255);
  @*/
void serialize_system_log_entry(
    const voting_system_secure_system_log_entry e,
    const char *ascii_encoded_system_log_entry[256]);

#endif /* __SYSTEM_LOG__ */
