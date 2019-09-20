# BVS Smart Ballot Box (SBB) Subsystem

The SBB is the top level component for the ballot box. At a high level, this
component is the state machine that mediates interaction between the human user
and the physical ballot box. The SBB is thus a client of the os, logging, and
crypto subsystems.

The implementations in sbb should be os-independent. The main loop should be
runnable in a POSIX context, where hardware inputs are simulated, and on an FPGA
running FreeRTOS with or without real hardware.

## API and Documentation

[The API](../include/sbb/sbb.h) is a refinement of
[sbb.lando](../../specs/lando/sbb/sbb.lando). The documentation, including
requirements, can be found there and in the associated lando specifications.

The logging format is discussed in [Logging.md](./Logging.md).

## Implementation

Most files are self-explanatory. The most important are: 

### `sbb.c`

This file contains implementations of most of the queries and commands from the
API, with the exception of the main loop.

### `sbb_crypto.c`

This file implements the procedures required to check if a ballot is valid
according to the cryptol and lando specifications:

- 1. The ballot should not be expired, meaning that the timestamp should denote
a time in the future; 
- 2. The ballot's MAC should be correct

### `sbb_logging.c`

This file implements the procedures required for logging both system events
(e.g., state changes) and application events (e.g., when ballots are cast and
spoiled). The file also implements the procedures that check to see if a given
ballot has already been cast or spoiled.

### `sbb_machine.c`

This file implements the main SBB state machine loop.

## Validation and Verification

### Dynamic Verification

Unit tests of the logging and crypto systems are in the [SBB test
directory](../tests/sbb), with the names `hosttestN`. Tests representing
complete scenarios are in the same directory, in the form of `expect` scripts
with names `sim_testN`.

### Static Verification

The axiomatic specification of the SBB, derived from `sbb.lando`, is located in
[sbb.acsl](../include/sbb/sbb.acsl). Specifications for the implementation are
given in ACSL, and we prove refinement between the axiomatic specification and
the actual implementation.
