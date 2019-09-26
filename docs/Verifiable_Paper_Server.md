# Verifiable Paper Server

## Executive Summary

The *Verifiable Paper Server* (VPS) is capable of managing and
authenticating dielets affixed to verifiable paper in accordance with
the BVS Protocol, discussed in [protocol.md](protocol.md).

## Overview

The Verifiable Paper Server is a secure database that associates and
authenticates physical election artifact paper reciepts with SHIELD
dielets embedded in them against cryptographically committed digital
interpretations of marked paper ballots. These links are be used to
prove that voters' selections were correctly interpreted and committed
to by the machine in the explicit and sole opinion of each voter in
question.

While in operation at a *Polling Place*, the VPS records in an
append-only fashion associations between cryptographic commitments
describing digital interpretations of paper ballots and identifiers
relating to the SHIELD dielets contained within the paper receipts
that these commitments are printed on.

When used in the *Post-Election* phase, the VPS will issue challenges
to the SHIELD dielets embedded within the paper receipts being
validated and authenticate the responses against identifiers
associated with each dielet.

## Manifest

@todo hmubarak An itemized list or table indicating where to find more information

## Glossary

@todo hmubarak point to the BVS 2020 and Free & Fair glossaries

## Requirements

@todo hmubarak/kiniry cite SOW requirements as appropriate

### Mandatory

 - *[BVS\_VPS\_Immutable]* The VPS must securely store persistent data in an immutable, append-only manner.
 - *[BVS\_VPS\_Record]* The VPS must record assciations between cryptographic commitments to digital interpretations of a ballot and SHIELD dielets embedded in paper receipts stating such commitments.
 - *[BVS\_VPS\_Evidence]* The VPS must send associations between commitments and dielets to the *Evidence Server*.
 - *[BVS\_VPS\_ChallengeResponse]* The VPS must issue challenges to and authenticate responses from SHIELD dielets.

### Optional

- *[BVS\_VPS\_Compare]* The VPS should be able to accept a log of associations from an *Evidence Server* and compare them against its internal records, flagging any and all discrepancies for review by the *Electoral Commission*.

## Documentation

@todo hmubark/kiniry manifest of documentation for the subsystem

## Validation and Verification Methodology

Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

@todo hmubarak/kiniry summary of our approach for this particular subsystem, including
a manifest of related artifacts.

## Contributors

@todo hmubarak Who worked on this particular subsystem.

## Funders

This project is funded by DARPA, via DARPA's SSITH and SHIELD programs,
under the Galois BESSPIN project. The Verifiable Paper Server is
designed and developed by Free & Fair in cooperation with Galois.

@todo kiniry Add appropriate verbiage here for DARPA attribution and other
SHIELD participants.