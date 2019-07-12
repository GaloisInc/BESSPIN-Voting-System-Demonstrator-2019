/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"

// String constant defines
const char *welcome_text = "Welcome, Voter!";
const char *insert_ballot_text = "Insert ballot...";
const char *barcode_detected_text = "Barcode detected";
const char *cast_or_spoil_line_1_text = " Cast or Spoil?";
const char *cast_or_spoil_line_2_text = "Spoil       Cast"; // spoil button on left
const char *casting_ballot_text = "Casting ballot.";
const char *spoiling_ballot_text = "Spoiling ballot.";
const char *invalid_barcode_text =  "Invalid barcode.";
const char *duplicate_barcode_line_1_text = "Ballot already ";
const char *duplicate_barcode_line_2_text = "cast or spoiled.";
const char *no_barcode_text = "No barcode.";
const char *remove_ballot_text = "Remove ballot...";

// HW event messages
#define HW_EVENT(msg) "HW event: " msg "."
log_entry sensor_in_pressed_msg            = HW_EVENT("Sensor in pressed");
log_entry sensor_in_released_msg           = HW_EVENT("Sensor in released");
log_entry sensor_out_pressed_msg           = HW_EVENT("Sensor out pressed");
log_entry sensor_out_released_msg          = HW_EVENT("Sensor out released");
log_entry cast_button_pressed_msg          = HW_EVENT("Cast button pressed");
log_entry cast_button_released_msg         = HW_EVENT("Cast button released");
log_entry spoil_button_pressed_msg         = HW_EVENT("Spoil button pressed");
log_entry spoil_button_released_msg        = HW_EVENT("Spoil button released");
log_entry barcode_scanned_msg              = HW_EVENT("Barcode scanned");
log_entry barcode_received_event_msg       = HW_EVENT("Received barcode");
log_entry empty_barcode_received_event_msg = HW_EVENT("Received empty barcode");

log_entry invalid_barcode_received_event_msg = HW_EVENT("Barcode is invalid");
log_entry decision_timeout_event_msg         = HW_EVENT("User cast/spoil decision timeout");
