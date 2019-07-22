/** Prototypes for non-public procedures used by sbb machine main loop */
#ifndef __SBB_MACHINE__
#define __SBB_MACHINE__

#include <FreeRTOS.h>
#include <task.h>
#include "log_t.h"

/*@ requires SBB_Machine_Invariant;
  @ requires 0 < length && length <= LOG_ENTRY_LENGTH;
  @ requires \valid_read(event_entry + (0 .. length - 1));
  @ assigns log_fs, the_state.L;
  @ ensures the_state.L != ABORT ==> the_state.L == \old(the_state.L);
  @ ensures SBB_Machine_Invariant;
*/
void log_single_event( EventBits_t event_bits,
                       EventBits_t log_bit,
                       const char* event_entry,
                       int length );

/*@ requires SBB_Machine_Invariant;
  @ assigns log_fs, the_state.L;
  @ ensures the_state.L != ABORT ==> the_state.L == \old(the_state.L);
  @ ensures SBB_Machine_Invariant;
*/
void log_event_group_result ( EventBits_t bits );

//@ assigns \nothing;
extern EventBits_t xEventGroupSetBits( EventGroupHandle_t xEventGroup,
                                       const EventBits_t uxBitsToSet );

// @todo abakst the ASM does not have NO_PAPER_DETECTED as reachable except from the initial
// state. Is this intentional?
/*@ requires SBB_Machine_Invariant;
  @ requires paper_in_pressed == true  || paper_in_pressed == false;
  @ requires paper_in_released == true || paper_in_released == false;
  @ assigns the_state.P, the_state.L, log_fs;
  @ ensures \old(the_state.L) == the_state.L || the_state.L == ABORT;
  @ ensures \old(the_state.P) == the_state.P
  @      || ASM_transition(\old(the_state), INTERNAL_PAPER_DETECT_E, the_state);
  @ ensures SBB_Machine_Invariant;
*/
void update_paper_state( bool paper_in_pressed,
                         bool paper_in_released );

/*@ requires SBB_Machine_Invariant;
  @ requires cast_button_pressed == true   || cast_button_pressed == false;
  @ requires cast_button_released == true  || cast_button_released == false;
  @ requires spoil_button_pressed == true  || spoil_button_pressed == false;
  @ requires spoil_button_released == true || spoil_button_released == false;
  @ assigns the_state.B, the_state.L, log_fs;
  @ ensures \old(the_state.B) == the_state.B
  @      || ASM_transition(\old(the_state), INTERNAL_CAST_SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), CAST_E, the_state);
  @ ensures SBB_Machine_Invariant;
  @ ensures \old(the_state.L) == the_state.L || the_state.L == ABORT;
*/
void update_button_state( bool cast_button_pressed,
                          bool cast_button_released,
                          bool spoil_button_pressed,
                          bool spoil_button_released );

/*@ requires SBB_Machine_Invariant;
  @ requires barcode_scanned == true || barcode_scanned == false;
  @ assigns the_state.BS, the_state.L, log_fs,
  @         barcode[0 .. BARCODE_MAX_LENGTH - 1], barcode_length;
  @ ensures the_state.L != ABORT ==> the_state.L == \old(the_state.L);
  @ ensures \old(the_state.BS) == the_state.BS
  @      || ASM_transition(\old(the_state), INTERNAL_BARCODE_E, the_state);
  @ ensures SBB_Machine_Invariant;
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

/*@ requires SBB_Machine_Invariant;
  @ assigns the_state.BS, the_state.L, the_state.P, the_state.B, log_fs;
  @ assigns barcode[0 .. BARCODE_MAX_LENGTH - 1], barcode_length;
  @ ensures
  @   (the_state.BS != \old(the_state).BS) ==>
  @     ASM_transition(\old(the_state), INTERNAL_BARCODE_E, the_state);
  @ ensures
  @   (the_state.B != \old(the_state).B) ==>
  @     (ASM_transition(\old(the_state), INTERNAL_CAST_SPOIL_E, the_state) ||
  @      ASM_transition(\old(the_state), SPOIL_E, the_state) ||
  @      ASM_transition(\old(the_state), CAST_E, the_state));
  @ ensures
  @   (the_state.P != \old(the_state).P) ==>
  @      ASM_transition(\old(the_state), INTERNAL_PAPER_DETECT_E, the_state);
  @ ensures the_state.L == ABORT || the_state.L == \old(the_state.L);
  @ ensures SBB_Machine_Invariant;
*/
void update_sensor_state(void);

// this is a workaround for multiple barcodes being "queued"
/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == STANDBY;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
  @ ensures the_state.M  == \old(the_state.M);
  @ ensures SBB_Machine_Invariant;
 */
void flush_barcodes(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == AWAIT_REMOVAL;
  @ ensures SBB_Machine_Invariant;
 */
void run_await_removal(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == EJECT;
  @ ensures SBB_Machine_Invariant;
 */
void run_eject(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == SPOIL;
  @ ensures SBB_Machine_Invariant;
 */
void run_spoil(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == CAST;
  @ ensures SBB_Machine_Invariant;
 */
void run_cast(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == WAIT_FOR_DECISION;
  @ ensures SBB_Machine_Invariant;
 */
void run_wait_for_decision(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == BARCODE_DETECTED;
  @ ensures SBB_Machine_Invariant;
*/
void run_barcode_detected(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == FEED_BALLOT;
  @ ensures SBB_Machine_Invariant;
 */
void run_feed_ballot(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == WAIT_FOR_BALLOT;
  @ ensures SBB_Machine_Invariant;
 */
void run_wait_for_ballot(void);

/*@ requires the_state.L == INITIALIZE;
  @ ensures SBB_Machine_Invariant;
 */
void run_initialize(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == STANDBY;
  @ ensures SBB_Machine_Invariant;
 */
void run_standby(void);

/*@ requires SBB_Machine_Invariant;
  @ requires the_state.L == ABORT;
  @ ensures SBB_Machine_Invariant;
  @ */
void run_abort(void);

#endif
