# Tabulation Device

## Executive Summary

A *Tabulation Device* computes the outcome(s) of an election from the
*Cast Vote Records* component of an election’s evidence.  For a
traditional election, such a tabulation is performed on cleartext
data, preferably in the simplest means possible, and is double-checked
through external tabulation of the same data (say, using a
spreadsheet).  For an E2E-V voting system, tabulation is accomplished
either via a decryption step (in the case of many mixnet-based
systems) or via homomorphic tabulation (as is the case with
ElectionGuard).
