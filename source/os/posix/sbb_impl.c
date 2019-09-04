#include "votingdefs.h"

// TBD move me
osd_event_mask_t           xSBBEventGroup;
osd_stream_buffer_handle_t xScannerStreamBuffer;

osd_timer_ticks_t
osd_get_ticks(void)
{
    //TBD
    osd_assert(0);
    return 0;
}

uint8_t
osd_read_time(struct voting_system_time_t *time)
{
    (void)time;
    //TBD
    osd_assert(0);
    return 0;
}


osd_event_mask_t
osd_event_group_set_bits(osd_event_group_handle_t event_group,
                         osd_event_mask_t         bits_to_set)
{
    (void)event_group;
    (void)bits_to_set;
    //TBD
    osd_assert(0);
    return 0;
}

osd_event_mask_t
osd_wait_for_event(osd_event_group_handle_t event_group,
                   osd_event_mask_t         bits_to_wait_for,
                   osd_event_clear_t        clear_on_exit,
                   osd_event_wait_type_t    wait_for_all_bits,
                   osd_timer_ticks_t        timeout)
{
    (void)event_group;
    (void)bits_to_wait_for;
    (void)clear_on_exit;
    (void)wait_for_all_bits;
    (void)timeout;
    //TBD
    osd_assert(0);
    return 0;
}

uint32_t osd_stream_buffer_receive(osd_stream_buffer_handle_t handle,
                                   void *pRxData,
                                   size_t xBufferLengthBytes,
                                   osd_timer_ticks_t max_block_time_ms)
{
    (void)handle;
    (void)pRxData;
    (void)xBufferLengthBytes;
    (void)max_block_time_ms;
    //TBD
    osd_assert(0);
    return 0;
}
