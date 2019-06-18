# BESSPIN Voting System Red Team Specification

This document summarizes the *purpose* of the hardware red team
exercise, the *threat model* for the demonstrator, and the *win
conditions* associated with specific red team milestones (such as DEF
CON 2019) and CPUs.

## purpose

To be cut-and-pasted from proposal documents.

## threat model

1. off Limits?
  1. secure boot
  2. AES Instructions??
2. load object file into memory
  1. gain access to protected memory via buffer error (BE)
  2. reveal "secret" information - via direct memory read, BE, ??
3. feed any single letter sized paper into ballot box
4. power cycle ballot box

## win conditions from the point of view of SSITH performers

0. compromise secure boot in order to run malware
1. physical attacks demonstrating compromise of the device
  1. flash lights in a particular fashion
  2. display specific text
2. buffer overflow attacks
  1. hijack SBB ASM or overwrite other protected data to:
     1. accept invalid ballot
     2. reject valid ballot
     3. cause a count of a cast ballot more or less than one time
     4. cause a count of a spoiled ballot one or more times
  2. manipulate a secret log in such a way as to change a bit and yet
     not be caught during verification
3. information leakage attacks
  1. exfiltrate AES authentication key stored in hardware on the SBB
     a. do we expose the AES key via a mem-mapped region and tell TA-1
     teams "thou shalt protect exactly these addresses!"
  2. decrypt secret data by revealing voter choices


4. are there any distinct ransomware attacks that we could describe as
   win conditions since the DoD cares about ransomware these days?
  1. encrypt logs with an attacker-defined key
  2. DoS SBB so that it refuses to accept any paper ballots


5. DoS attacks on reporting infrastructure?
  1. prevent the SBB's election reporting task from running
  2. prevent the SBB's election reporting task from communicating to
     the election server

6. Is there any system-defined values used at runtime and memory
   mapped that would cause havoc if changed?
  1. Ethernet buffer?
