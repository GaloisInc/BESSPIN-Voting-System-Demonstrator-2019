# Evidence Server

## Executive Summary

An *Evidence Server* (ES) (also known as a *Bulletin Board* in the E2E-V
literature) shares all evidence of an election to the public using
open common data, machine readable, formats.

For a traditional voting system, the ES publishes the results of the
election and public metadata on the election, such as the time and
date of the election, the EOs responsible for the election, all of the
ballot styles of the election, example blank ballot images for every
style, total number of voters checked in, total number of ballots cast
and counted, under/overcounts per contest, etc.

For an E2E-V voting system, the ES also publishes the cryptographic
evidence of the election so that independent third parties can both
double-check the announced results of the election (via independent
tabulation) and verify the election’s evidence (via E2E-V
verification).  The ES also facilitates the lookup of a ballot receipt
in an election’s evidence, so as to prove to a voter that the
encryption performed by the PBS was, in fact, accurate.

## Overview

The evidence server is responsible for collecting, and subsequently making
available, all of the evidence generated during the election. This includes:

- Election metadata (date, time, the officials at each polling place, and so on)
- Records of certification of voter registration containing: (from Registration System)
  - The voter authenticator
  - The registration system
  - The polling place
  - The voter
- Records linking voters to their ballot style (from Ballot Printing System)
- Marked ballot images (from Ballot Scanning Device)
- Ballot receipts (from Ballot Scanning Device)
- Ballot outcome records:
- Spoiled ballots (from Controller System, Verifiable Paper System)
- Cast ballots (from Ballot Scanning Device)
- Records of challenged ballots (from Ballot Scanning Device)
- SBB Logs documenting cast ballots
- Tabulation Logs (from the Tabulation Device)
- Decrypted challenged and spoiled ballots (available only after the election)

@design abakst gajaka : how is evidence represented to the user (raw records of the above? Some standard or uniform format?)

## Manifest

The main artifacts to read to better understand what the background is on the
Evidence Server,

- The original STAR-Vote paper "STAR-Vote: A Secure, Transparent, Auditable, and
  Reliable Voting System" by Bell,
- "Public Evidence from Secret Ballots" by Bernhard,
- "End-to-end verifiability" by Benaloh.

@todo an itemized list or table indicating where to find more information

## Glossary

@todo point to the BVS 2020 and Free & Fair glossaries

## Requirements

The evidence server’s requirements are derived from the overall BVS 2020 system
goal of implementing an end-to-end verifiable election. Thus, the mandatory
requirements are as follows:
- [Stability] Only items that have been posted can appear on the Bulletin Board.
- [Confirmability] Any item with a valid receipt must appear on the Bulletin Board.
- [Soundness] No clashing items must both appear on the Bulletin Board.
- [Unremovability] Once published, no items can be removed from the Bulletin Board.
- [Persistence] Data should be immutable and persistent.
- [Challenge] Using the evidence server, voters can use the election server to verify that their challenged ballots are correctly recorded.
- [CollectedAsCast] Using the evidence server, voters can independently verify that the representation of their vote is correctly collected in the tally. 
- [TalliedAsCollected] Using the evidence server, anyone can verify that every well-formed,collected vote is correctly included in the tally.
- [VoterConfidentiality] Personally identifiable information should not be exposed, in particular there should be no evidence about how and given person voted.
- [Compliance] Exposed data is subject to relevant privacy laws.
- [Availability] The election server should remain available under heavy load.
- [Timing] All evidence should include a timestamp indicating when the evidence was generated.

## Documentation

@todo manifest of documentation for the subsystem

## Validation and Verification Methodology

- The recorded-as-cast verification is provided by the publication of a list of all the encrypted votes that have been submitted. 
- Every honest voter who receives a valid receipt is assured that her vote will be published on the evidence server and included in the election tally. 
  A voter is able to check himself using the tracking number that his vote is included.
- The evidence server provide cryptographically strong evidence that a voter’s receipt corresponds to a ballot, on the bulletin board.



Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

@design abakst gajaka need to discuss a realistic approach to validation verification

## Contributors

Joe Kiniry, Alexander Bakst, Dragan Stosic

## Funders

@todo indicate DARPA's support and indicate if any other agencies
contributed resources
