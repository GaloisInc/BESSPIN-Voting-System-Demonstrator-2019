# Static Assurance

## Completeness

Currently, there exist contracts that Frama-C/WP can not prove automatically,
due to compleness issues with Alt-Ergo.

## Memory Model

This module should be verified using the Typed+Cast memory model, as the Typed
memory model is unable to handle frequently required conversions, such as
between `unsigned char` and `char` pointers.

## Strings

Facts about strings are currently assumed by a function `__assume_strings_OK`,
in order to temporarily work around issues with Frama-C and string literals.

# Dynamic Assurance

`hosttestN`.c are unit tests, specifically testing that
the SBB correctly recognizes and rejects correct and invalid barcodes,
respectively. `sim_testN` are `expect` scripts that test the entire ballot box
in its POSIX simulation mode.
