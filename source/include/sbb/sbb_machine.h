/** Prototypes for non-public procedures used by sbb machine main loop */
#ifndef __SBB_MACHINE__
#define __SBB_MACHINE__

#include "votingdefs.h"
#include "logging/log_t.h"

/* How long we wait to receive a scanned barcode */
#define SCANNER_BUFFER_RX_BLOCK_TIME_MS osd_msec_to_ticks(15)

/**
 * @mpodhradsky
 * Adding missing function declarations
 */
void take_step(void);
logic_state debug_state_change(logic_state then, logic_state now);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires 0 < length && length <= LOG_ENTRY_LENGTH;
  @ requires \valid_read(event_entry + (0 .. length - 1));
  @ assigns log_fs, the_state.FS;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void log_single_event( osd_event_mask_t event_bits,
                       osd_event_mask_t log_bit,
                       const char* event_entry,
                       int length );

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ assigns log_fs, the_state.FS;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void log_event_group_result ( osd_event_mask_t bits );

// @todo abakst the ASM does not have NO_PAPER_DETECTED as reachable except from the initial
// state. Is this intentional?
/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires paper_in_pressed == true  || paper_in_pressed == false;
  @ requires paper_in_released == true || paper_in_released == false;
  @ assigns the_state.P, the_state.FS, log_fs;
  @ ensures \old(the_state.P) == the_state.P
  @      || ASM_transition(\old(the_state), INTERNAL_PAPER_DETECT_E, the_state);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void update_paper_state( bool paper_in_pressed,
                         bool paper_in_released );

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires cast_button_pressed == true   || cast_button_pressed == false;
  @ requires cast_button_released == true  || cast_button_released == false;
  @ requires spoil_button_pressed == true  || spoil_button_pressed == false;
  @ requires spoil_button_released == true || spoil_button_released == false;
  @ assigns the_state.B, the_state.FS, log_fs;
  @ ensures \old(the_state.B) == the_state.B
  @      || ASM_transition(\old(the_state), INTERNAL_CAST_SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), SPOIL_E, the_state)
  @      || ASM_transition(\old(the_state), CAST_E, the_state);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void update_button_state( bool cast_button_pressed,
                          bool cast_button_released,
                          bool spoil_button_pressed,
                          bool spoil_button_released );

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires barcode_scanned == true || barcode_scanned == false;
  @ assigns the_state.BS, the_state.FS, log_fs,
  @         barcode[0 .. BARCODE_MAX_LENGTH - 1], barcode_length;
  @ ensures \old(the_state.BS) == the_state.BS
  @      || ASM_transition(\old(the_state), INTERNAL_BARCODE_E, the_state);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void update_barcode_state( bool barcode_scanned );

// This refines the internal paper ASM event
//@ assigns \nothing;
osd_event_mask_t next_paper_event_bits(void);

// This refines the internal button ASM event
//@ assigns \nothing;
osd_event_mask_t next_button_event_bits(void);

//@ assigns \nothing;
osd_event_mask_t next_barcode_event_bits(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ assigns the_state.BS, the_state.FS, the_state.P, the_state.B, log_fs;
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
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void update_sensor_state(void);

// this is a workaround for multiple barcodes being "queued"
/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == STANDBY;
  @ assigns the_state.FS, the_state.BS, barcode[0 .. BARCODE_MAX_LENGTH - 1], barcode_length,
  @         the_state.P, the_state.B, log_fs;
  @ ensures the_state.BS == BARCODE_NOT_PRESENT;
  @ ensures the_state.M  == \old(the_state.M);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void flush_barcodes(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == AWAIT_REMOVAL;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_await_removal(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == EJECT;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_eject(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == SPOIL;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_spoil(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == CAST;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_cast(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == WAIT_FOR_DECISION;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_wait_for_decision(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == BARCODE_DETECTED;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
*/
void run_barcode_detected(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == FEED_BALLOT;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_feed_ballot(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == WAIT_FOR_BALLOT;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_wait_for_ballot(void);

/*@ requires the_state.L == INITIALIZE;
  @ requires !Log_IO_Initialized;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_initialize(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ requires the_state.L == STANDBY;
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
 */
void run_standby(void);

/*@ requires SBB_Machine_Invariant(the_state, gpio_mem);
  @ ensures SBB_Machine_Invariant(the_state, gpio_mem);
  @ */
void run_abort(void);

#endif
