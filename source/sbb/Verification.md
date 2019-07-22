# Verification Status

## Strings

Facts about strings are current assumed by a function `__assume_strings_OK`, in
order to temporarily work around issues with Frama-C and string literals.

## Logging

`make wp` currently fails to verify a call to `Log_IO_File_Exists`. This call
should succeed once the contract of `Log_IO_File_Exists` is weakened to require
`valid_read_string`, not `valid_string`.
