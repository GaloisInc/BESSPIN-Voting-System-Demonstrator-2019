/**
 * Smart Ballot Box API
 * @refine sbb.lando
 */

#include "sbb.h"

// String constant defines
const char *empty = " ";
const char *welcome_text = "Welcome, Voter!";
const char *insert_ballot_text = "Insert ballot...";
const char *barcode_detected_text = "Barcode detected";
const char *cast_or_spoil_line_1_text = " Cast or Spoil?";
const char *cast_or_spoil_line_2_text = "Spoil       Cast"; // spoil button on left
const char *casting_ballot_text = "Casting ballot.";
const char *spoiling_ballot_text = "Spoiling ballot.";
const char *invalid_barcode_text =  "Invalid ballot.";
const char *duplicate_barcode_line_1_text = "Ballot already ";
const char *duplicate_barcode_line_2_text = "cast or spoiled.";
const char *no_barcode_text = "No ballot found.";
const char *remove_ballot_text = "Remove ballot...";
const char *error_line_1_text = " A fatal error";
const char *error_line_2_text = "    occurred";

// HW event messages
const char *sensor_in_pressed_msg            = "Sensor in pressed";
const char *sensor_in_released_msg           = "Sensor in released";
const char *sensor_out_pressed_msg           = "Sensor out pressed";
const char *sensor_out_released_msg          = "Sensor out released";
const char *cast_button_pressed_msg          = "Cast button pressed";
const char *cast_button_released_msg         = "Cast button released";
const char *spoil_button_pressed_msg         = "Spoil button pressed";
const char *spoil_button_released_msg        = "Spoil button released";
const char *barcode_scanned_msg              = "Barcode scanned";
const char *barcode_received_event_msg       = "Received barcode";
const char *empty_barcode_received_event_msg = "Received empty barcode";

const char *invalid_barcode_received_event_msg = "Barcode is invalid";
const char *decision_timeout_event_msg         = "User cast/spoil decision timeout";

void __assume_strings_OK() { }
