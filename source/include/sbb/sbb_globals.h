/**
 * Smart Ballot Box Global Definitions
 * @refine sbb.lando
 */
#ifndef __SBB_GLOBALS_H__
#define __SBB_GLOBALS_H__

// General includes
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

// Subsystem includes
#include "sbb_t.h"
#include "log_t.h"

extern char barcode[BARCODE_MAX_LENGTH];
extern barcode_length_t barcode_length;

// Per-ballot-box data
extern const char *sbb_name; // the SBB name, for display
extern const log_name system_log_file_name; // the system log
extern const log_name app_log_file_name; // the application log
// note there are two different MAC address variables, both of which are actually used
// currently, AxiEthernetMAC is always initialized with the contents of sbb_mac_address
// before network stack initialization
extern const uint8_t sbb_mac_address[6]; // the MAC address used by part of the IP stack
extern char AxiEthernetMAC[6]; // the MAC address used by the AXI interface
extern const uint8_t sbb_default_ip_address[4]; // in case DHCP doesn't work
extern const uint8_t sbb_default_netmask[4]; // in case DHCP doesn't work
extern const uint8_t sbb_default_gateway_address[4]; // in case DHCP doesn't work
extern const uint8_t sbb_default_dns_server_address[4]; // in case DHCP doesn't work
extern const uint16_t sbb_log_port_number;

// Display strings
extern const char *empty;
extern const char *welcome_text;
extern const char *insert_ballot_text;
extern const char *barcode_detected_text;
extern const char *cast_or_spoil_line_1_text;
extern const char *cast_or_spoil_line_2_text;
extern const char *casting_ballot_text;
extern const char *spoiling_ballot_text;
const char *expired_ballot_line_1_text;
const char *expired_ballot_line_2_text;
extern const char *invalid_barcode_text;
extern const char *duplicate_barcode_line_1_text;
extern const char *duplicate_barcode_line_2_text;
extern const char *no_barcode_text;
extern const char *remove_ballot_text;
extern const char *error_line_1_text;
extern const char *error_line_2_text;

extern SBB_state the_state;

// @spec abakst Specifications needed for for hardware, related to the
// above I think we probably want some ghost `uint8_t` array to model
// these reads/writes.
extern uint8_t gpio_mem[8];
#endif
