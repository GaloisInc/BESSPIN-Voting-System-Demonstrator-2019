# Smart Ballot Box

## Executive Summary

A *Smart Ballot Box* (SBB for short) permits a voter to securely store
a legal, marked paper ballot. The main function of the SBB is to
accept and store a legal ballot for the current election and reject
ballots that are not part of the current election.

## Overview

When a voter is ready to cast their ballot they may insert their marked
ballot into the SBB. The ballot is then held in a temporary location
out of physical reach.

The SBB scans a 1D/2D barcode located on the paper ballot and the
encoded barcode information is forwarded to the *Controller*.
The controller makes a determination regarding the validity of the
ballot, taking into consideration the timeliness, uniqueness, and
correctness of the ballot, and returns that result to the SBB.

If the controller rejects the ballot, the ballot will be ejected
from the paper feeder, the reason for rejection will be logged by
the logging subsystem and an error message displayed to the voter.

@design osborn.steven: This paragraph is all assumptions on my part.

If a local network error, controller error, or time window expires,
resulting in an unexpected condition the SBB will eject the
ballot. The SBB will then report the error to the logging subsystem
and display a message to the voter.  Once connectivity to the 
controller is restored the ballot may be recast as long as the ballot
has not expired.

If the ballot is determined by the controller to be correct and 
countable for the current election, the voter will be prompted via
the SBB UI to either cast or spoil their ballot.

A voter may cast their ballot by pressing the cast button triggering
the SBB paper feeder to advance the ballot completely into the SBB
secure container where it is stored until the end of the election.
Once a ballot is cast, a duplicate ballot with the same barcode will
be rejected by any SBB communicating with the controller for that
election.

@design: osborn.steven Should there be an exception for SBB emptied mid election.  Concerns on state kept on the SBB or controller?

A voter may also choose to spoil their ballot because of a marking error
or change of heart.  They may also choose to spoil their ballot as a
method of challenging the voting terminal.  A spoiled ballot is recorded
as such and the ballot ejected from the SBB. A spoiled ballot document
must be visibly marked as spoiled and must not be recast.

The SBB allows officials and voters to challenge the BVS by trying to
cast an invalid ballot which would be rejected or inserting a valid
test ballot which may be spoiled, thus not tabulating the test ballot
result as part of the election.

All ballot actions, external events, as well as internal device
state-machine changes are communicated to the logging subsystem and
must be stored in the evidence server for verifiability.

## Manifest

SBB artifacts:
  1. SBB *development plan*, which is a part of the overall BVS 2020 plan.
  2. SBB description (this file)
  3. SBB [formal specifications](../specs/lando/sbb)

## Glossary

Our system glossary is based upon the 
[Free & Fair Election Glossary](https://github.com/FreeAndFair/ElectionGlossary), 
which is in turn based upon the 
[NIST Election Glossary](https://pages.nist.gov/ElectionGlossary/).

## Requirements

@todo osborn.steven summarize the overall framing and depth of the requirements

### Mandatory

- *[BVS-SBB-FeedIn]* Ingest paper.
- *[BVS-SBB-FeedOut]* Eject paper.
- *[BVS-SBB-DetectPaper]* Detect paper presence.
- *[BVS-SBB-ScanBarcode]* Scan 1D/2D Barcode.
- *[BVS-SBB-Verify]* Verify cryptographic barcode with controller.
- *[BVS-SBB-Display]* The SBB must be present the voter with cast / spoil
  instructions as well as display current state information.
- *[BVS-SBB-Selection]* The SBB must provide physical means to allow a
     voter to choose to spoil or cast a vote.
- *[BVS-SBB-Log]* The SBB must send all state changes and events to
     the logging system.
- *[BVS-SBB-Evidence]* SBB must export all logs to evidence server.

## Documentation

At this time this document is the only documentation for the BPS system.  The
overall description of the BESSPIN Voting System 2020 is found in its [parent
description](BVS 2020 system description.md).

## Validation and Verification Methodology

Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

@todo osborn.steven summary of our approach for this particular subsystem, including
a manifest of related artifacts.

## Contributors

  * Steven Osborn wrote this subsystem description.

## Funders

@todo osborn.steven indicate DARPA's support and indicate if any other agencies contributed resources
