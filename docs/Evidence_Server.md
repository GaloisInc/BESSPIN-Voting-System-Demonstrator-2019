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

The Evidence Server is responsible for collecting, and subsequently making
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

## Manifest

This subsystem's artifacts are found in the following locations:

- [Development Plan](../specs/evidence_server/plan.lando).
- _Documentation_: TBD
- _Specification_: TBD
- _Source Code_: TBD

The following issues track the design and development of this
subsystem:

- _Development Plan_: #176
- _System Description_: #177
- _Threat Model_: #179
- _Domain Model_: #178

The following is a list of background reading to give context for the evidence
server.

- "STAR-Vote: A Secure, Transparent, Auditable, and Reliable Voting System" by
  Bell, et al.
  [PDF](https://www.usenix.org/system/files/conference/evtwote13/jets-0101-bell.pdf)
- "Public Evidence from Secret Ballots" by Bernhard, et al.
  [PDF](https://arxiv.org/pdf/1707.08619.pdf)
- "End-to-end verifiability" by Benaloh, et al.
  [PDF](https://arxiv.org/ftp/arxiv/papers/1504/1504.03778.pdf)


## Glossary

Our system glossary is based upon the 
[Free & Fair Election Glossary](https://github.com/FreeAndFair/ElectionGlossary),
which is in turn based upon the 
[NIST Election Glossary](https://pages.nist.gov/ElectionGlossary/).


## Requirements

The Evidence Server’s requirements are derived from the overall BVS 2020 system
goal of implementing an end-to-end verifiable election. Thus, the mandatory
requirements are as follows.

### Mandatory

- [EvidenceBounds] Evidence available from the server is always signed and
  verifiable evidence for the election.

- [Confirmability] Any unit of evidence with a valid receipt must be available
  from the evidence server.

- [Permanence] Once published, a unit of evidence must not be removed from the
  evidence server.

- [Immutability] Evidence stored on the evidence server must be immutable.

- [Challenge] The evidence server's interface must enable users to verify
  challenged ballots.

- [CollectedAsCast] The evidence server's interface must enable users to
  verify that a given receipt appears in the list of collected ballots.

- [TalliedAsCollected] The evidence server's interface must enable users to
  download the collection of encrypted, cast ballots.

- [VoterConfidentiality] The evidence server's interface must not allow users to
  to learn secret information about voters.

- [VerifyElection] The evidence server's interface must allow users to download
  the complete evidence for the election.

- [Compliance] The evidence server's interface must expose information only in
  accordance with relevant privacy laws.

### Optional

- [Availability] The election server should remain available under heavy load.

## Documentation

This document is currently the only documentation for the Evidence Server. The
overall description of the BESSPIN Voting System 2020 is found in its
[parent description](./BVS_2020_system_description.md).

## Validation and Verification Methodology

Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

@design abakst, gajaka: need to discuss a realistic approach to validation verification

## Contributors

 - Alexander Bakst worked on this subsystem description.
 - Dragan Stosic worked on this subsystem description.
 - Joe Kiniry worked on this subsystem description.

## Funders

@todo abakst: indicate DARPA's support and indicate if any other agencies
contributed resources
