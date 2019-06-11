# BESSPIN Voting System Red Team Specification

This document summarizes the *purpose* of the hardware red team
exercise, the *threat model* for the demonstrator, and the *win
conditions* associated with specific red team milestones (such as DEF
CON 2019) and CPUs.

## Purpose

To be cut-and-pasted from proposal documents.

## Threat Model

1. off Limits
  1. secure boot
  2. AES Instructions??
2. load object file into memory
  1. gain access to protected memory via BOE
  2. reveal "secret" information - via direct memory read, BOE, ??
3. feed any single letter sized paper into ballot box
4. power cycle ballot box

## Win Conditions

1. physical
  1. flash lights 
  2. display text
2. buffer overflow
  1. hijack SBB ASM or overwrite other protected data to:
     1. accept invalid ballot
     2. reject valid ballot
     3. count a ballot more or less than one time
3. information leakage
  1. exfiltrate AES key
  2. reveal ballot data <- via use of AES key


