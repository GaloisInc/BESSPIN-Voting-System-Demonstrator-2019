/**
 * Smart Ballot Box HW Abstraction API
 * @refine sbb.lando
 */
#include "sbb_hw.h"
#include "FreeRTOS.h"
#include "debug_io.h"
#include "ds1338rtc.h"


bool hw_get_current_time(uint32_t *year, uint16_t *month, uint16_t *day,
                         uint16_t *hour, uint16_t *minute)
{
#ifdef SIMULATION_UART
    // no RTC in the UART-only simulation
    (void) year;
    (void) month;
    (void) day;
    (void) hour;
    (void) minute;
    return true;
#else // SIMULATION_UART
    static struct rtctime_t time;
#ifdef HARDCODE_CURRENT_TIME
    time.year = CURRENT_YEAR - 2000;
    time.month = CURRENT_MONTH;
    time.day = CURRENT_DAY;
    time.hour = CURRENT_HOUR;
    time.minute = CURRENT_MINUTE;
#else
    configASSERT(ds1338_read_time(&time) == 0);
#endif /* HARDCODE_CURRENT_TIME */

    *year = (uint32_t)time.year + 2000;
    *month = (uint16_t)time.month;
    *day = (uint16_t)time.day;
    *hour = (uint16_t)time.hour;
    *minute = (uint16_t)time.minute;

#ifdef VOTING_SYSTEM_DEBUG
    // A character array to hold the string representation of the time
    static char time_str[20];
    format_time_str(&time, time_str);
    printf("Get current time: %s\r\n",time_str);
#endif
    return true;
#endif // SIMULATION_UART
}
