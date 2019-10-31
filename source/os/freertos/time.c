#include "votingdefs.h"

uint8_t
osd_read_time(struct voting_system_time_t *time)
{
#ifndef SIMULATION
    struct rtctime_t rtc_time;
    ds1338_read_time(&rtc_time);

    time->year   = rtc_time.year;
    time->month  = rtc_time.month;
    time->day    = rtc_time.day;
    time->hour   = rtc_time.hour;
    time->minute = rtc_time.minute;
#else
    (void)time;
#endif /* SIMULATION */

    return 0;
}

void
osd_format_time_str(struct voting_system_time_t *time, char *buf)
{
    struct rtctime_t rtc_time;
    rtc_time.year   = time->year;
    rtc_time.month  = time->month;
    rtc_time.day    = time->day;
    rtc_time.hour   = time->hour;
    rtc_time.minute = time->minute;

    format_time_str(&rtc_time, buf);
}
