/** Prototypes for non-public procedures used by sbb machine main loop */
#include <FreeRTOS.h>
#include <task.h>
#include "log_t.h"

void log_single_event( EventBits_t bits,
                       EventBits_t bit,
                       const log_entry event_entry );

void log_event_group_result ( EventBits_t bits );

//@ assigns \nothing;
extern EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                       const EventBits_t uxBitsToSet );

// @todo abakst the ASM does not have NO_PAPER_DETECTED as reachable except from the initial
// state. Is this intentional?
/*@ assigns the_state.P;
  @ ensures \old(the_state.P) == the_state.P
  @      || ASM_transition(\old(the_state), INTERNAL_PAPER_DETECT_E, the_state);
*/
void update_paper_state( bool paper_in_pressed,
                         bool paper_in_released );

/*@ assigns the_state.B;
  @ ensures \old(the_state) == the_state
  @      || ASM_transition(\old(the_state), INTERNAL_CAST_SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), CAST_E, the_state);
*/
void update_button_state( bool cast_button_pressed,
                          bool cast_button_released,
                          bool spoil_button_pressed,
                          bool spoil_button_released );

/*@ assigns the_state.BS;
  @ ensures \old(the_state) == the_state
  @      || ASM_transition(\old(the_state), INTERNAL_BARCODE_E, the_state);
*/
void update_barcode_state( bool barcode_scanned );

// This refines the internal paper ASM event
//@ assigns \nothing;
EventBits_t next_paper_event_bits(void);

// This refines the internal button ASM event
//@ assigns \nothing;
EventBits_t next_button_event_bits(void);

//@ assigns \nothing;
EventBits_t next_barcode_event_bits(void);


/*@ ensures
  @ \exists SBB_state s1, SBB_state s2;
  @      (s1 == \old(the_state) || ASM_transition(\old(the_state), INTERNAL_PAPER_DETECT_E, s1))
  @      && (s2 == s1 || ASM_transition(s1, INTERNAL_CAST_SPOIL_E, s2)
  @                   || ASM_transition(\old(the_state), SPOIL_E, the_state)
  @                   || ASM_transition(\old(the_state), CAST_E, the_state))
  @      && (the_state == s2 || ASM_transition(s2, INTERNAL_BARCODE_E, the_state));
*/
void update_sensor_state(void);

/*@ assigns the_state.BS;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
 */
void flush_barcodes(void);

/*@ requires the_state.L == AWAIT_REMOVAL;
 */
void run_await_removal(void);

/*@ requires the_state.L == EJECT;
 */
void run_eject(void);

/*@ requires the_state.L == SPOIL;
 */
void run_spoil(void);

/*@ requires the_state.L == CAST;
 */
void run_cast(void);

/*@ requires the_state.L == WAIT_FOR_DECISION;
 */
void run_wait_for_decision(void);

/*@ requires the_state.L == BARCODE_DETECTED;
 */
void run_barcode_detected(void);

/*@ requires the_state.L == FEED_BALLOT;
 */
void run_feed_ballot(void);

/*@ requires the_state.L == WAIT_FOR_BALLOT;
 */
void run_wait_for_ballot(void);

/*@ requires the_state.L == INITIALIZE;
 */
void run_initialize(void);

/*@ requires the_state.L == STANDBY;
 */
void run_standby(void);
