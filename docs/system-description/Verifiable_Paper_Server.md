# Verifiable Paper Server

## Executive Summary

The *Verifiable Paper Server* (VPS) is capable of managing and
authenticating **SHIELD dielets affixed to verifiable paper**
against **interpretation commitments** in accordance with
the BVS Protocol, discussed in [protocol.md](protocol.md).

## Overview

The Verifiable Paper Server is a secure, publicly-accessible server
that associates and authenticates physical election artifact paper
reciepts with SHIELD dielets embedded in them against cryptographically
committed digital interpretations of marked paper ballots. These links
are be used to prove that voters' selections were correctly interpreted
and committed to by the machine in the explicit and sole opinion of
each voter in question.

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

@todo hmubarak: an itemized list or table indicating where to find
more information

The VPS subsystem thus far has the following artifacts:

1. The VPS *development plan*, which is a part of the overall BVS 2020 plan.
2. This VPS [description itself](#verifiable-paper-server).

The VPS subsystems is heavily dependent upon technology developed as
part of the DARPA SHIELD (Supply Chain Hardware Integrity for
Electronics Defense) program; more information about that program is
available as follows:

1. DARPA MTO [Program Information](https://www.darpa.mil/program/supply-chain-hardware-integrity-for-electronics-defense)
2. Software and Supply Chain Assurance Winter Forum 2018 [Presentation](https://csrc.nist.gov/CSRC/media/Projects/cyber-supply-chain-risk-management/documents/SSCA/Winter_2018/TuePM2.1-SHIELD.pdf)
3. Galois [Press Release](https://galois.com/news/galois-awarded-darpa-subcontract-to-strengthen-supply-chain-protection-of-electronic-components/)
4. SRI International [Press Release](https://www.sri.com/newsroom/press-releases/sri-international-selected-darpa-develop-artificial-intelligence-system)
5. [Secure and Efficient Initialization and Authentication Protocols for SHIELD](https://eprint.iacr.org/2015/210.pdf)

## Glossary

Our system glossary is based upon the [Free & Fair Election Glossary][],
which is in turn based upon the [NIST Election Glossary][].

[Free & Fair Election Glossary]: https://github.com/FreeAndFair/ElectionGlossary
[NIST Election Glossary]: https://pages.nist.gov/ElectionGlossary/

## Requirements

**BESSPIN Voting System (Subsystems Description):**

 > 11. In order to support the use of SHIELD-based Verifiable Paper
 > (VP) in the BVS 2020 system, we must develop a SHIELD VP Server
 > (VPS), capable of managing and authenticating dielets affixed to
 > verifiable paper in accordance with the BVS Protocol, discussed
 > below.

 _editor's note: there is no further discussion of the VPS in SOW_

### Mandatory

 - *[BVS-VPS-Log]* The VPS must securely log persistent data in an immutable,
   append-only manner.
 - *[BVS-VPS-Record]* The VPS must record associations between cryptographic
   commitments to digital interpretations of a ballot and SHIELD dielets
   embedded in paper receipts stating such commitments.
 - *[BVS-VPS-Evidence]* The VPS must send associations between commitments and
   dielets to the *Evidence Server*.
 - *[BVS-VPS-ChallengeResponse]* The VPS must issue challenges to and
   authenticate responses from SHIELD dielets.
 - *[BVS-VPS-Authentication]* The VPS must securely authenticate bidirectionally
   with both the *Evidence Server* and the *Ballot Scanning Device* prior to
   transmitting or receiving any non-authentication data.
 - *[BVS-VPS-Communication]* The VPS must ensure that all communications between
   itself and both the *Evidence Server* and *Ballot Scanning Device* are
   secure.

### Optional

- *[BVS-VPS-Compare]* The VPS should be able to accept a log of associations
  from an *Evidence Server* and compare them against its internal records,
  flagging any and all discrepancies for review by the *Electoral Commission*.
- *[BVS-VPS-ReuseWork]* The implementation of the VPS should reuse work from the
  reference SHIELD server as much as is useful.

## Documentation

@todo hmubarak: manifest of documentation for the subsystem

At this time this document is the only documentation for the VPS system.
The overall description of the BESSPIN Voting System 2020 is found in its
[parent description](BVS 2020 system description.md).

## Validation and Verification Methodology

Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

The VPS subsystem's specification and assurance will be guaranteed
through our formalization of the overall BVS 2020 workflow and protocol.
In  particular, every requirement listed above must be shown to be
valid in that protocol description.

As the VPS is mainly a realization of technology interacted with in a
relatively straightforward manner, it is not expected that there will
be a human behavioral action that will cause the subsystem to violate
the invariants as enumerated in [Requirements](#requirements).

## Contributors

@todo hmubarak: who worked on this particular subsystem.

 - Haneef Mubarak wrote this (VPS) subsystem description.

The development of this subsystem would also not have been possible
without the efforts of our collaborators at [SRI International][] and
[TOZNY][], who developed the hardware and software that together
composes the SHIELD dielet system, respectively.

[SRI International]: https://www.sri.com
[TOZNY]: https://tozny.com

## Funders

This project is funded by DARPA, via DARPA's SSITH and SHIELD programs,
under the Galois BESSPIN project. The Verifiable Paper Server is
designed and developed by Free & Fair in cooperation with Galois.

@todo kiniry: add appropriate verbiage here for DARPA attribution and other
SHIELD participants.
