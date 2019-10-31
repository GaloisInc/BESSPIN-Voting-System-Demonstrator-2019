# Registration System

## Executive Summary

A *Registration System* (also known as an *Electronic Pollbook*, or
*ePollbook* for short) is used to facilitate the identification of
legal voters in a specific polling place or vote center.  Voters that
are permitted to vote are associated with a *Ballot Style*.  Voters
that are in the wrong polling place are redirected to their proper
polling place.  Voters that are not permitted to vote are turned away.
Each of these actions is logged for the authorities.  Voters are only 
permitted to vote once in an election.

## Overview

When a voter walks into the polling place to vote, the voter’s
identity is validated against the voter registration database, which
is contained in the Registration System.  After an election official
checks the voter’s identity against the registration system, one
of several events may occur:

* the voter is verified as a registered voter, persistently recorded
  as having checked in, and provided an appropriate ballot style for
  voting,

* the voter is not already registered in the registration system and
  provides evidence that he/she should be allowed to vote. In this
  case, the voter may be added to the registration system,
  persistently recorded as having checked in, and provided an
  appropriate ballot style for voting.

* the voter is registered, but is recorded as having checked in. 
  In this case, the voter can either:

     * contest the claim that they have already checked in, in which
       case the voter record is flagged for further investigation and 
       the voter is redirected to an election official.

     * confirm that he/she did already vote and subsequently exit the
       voting process.

## Manifest

This subsystem's artifacts are in the following locations:

- [Development Plan](../specs/lando/registration_system/plan.lando)
- _Documentation_: No documentation beyond this file exists at present.
- [Specification](../specs/lando/registration_system)
- _Source Code_: No source code exists at present.
- [Code repository for BVS 2020](https://gitlab-ext.galois.com/ssith/voting-system)

The following issues track the design and development of this subsystem:

- _Development Plan_: #181
- _System Description_: #182
- _Threat Model_: #185
- _Domain Model_: #183

## Glossary

Our system glossary is based upon the 
[Free & Fair Election Glossary](https://github.com/FreeAndFair/ElectionGlossary), 
which is in turn based upon the 
[NIST Election Glossary](https://pages.nist.gov/ElectionGlossary/).

## Requirements

The following are the mandatory and optional requirements imposed upon
the BVS 2020 Registration System.  Informal verification (in the
traditional software engineering sense) of these requirements is
accomplished by several means, including formal verification of
properties of the system's specification and implementation and 
traceability from the requirements to artifacts that validate their
satisfaction (e.g., system tests, code review, etc.).

Our requirements language loosely follows 
[RFC 2119](https://www.ietf.org/rfc/rfc2119.txt). Mandatory requirements 
use the modal verb _must_; requirements that are strongly recommended 
use the modal verb _should_; truly optional requirements use the modal 
verb _may_. 

The top-level requirements are as follows.

### Mandatory

 * *[AUTHENTICATE_VOTER]* Must be able to authenticate a voter.
 * *[VOTER_STYLE]* Must identify the correct ballot style for the
   voter.
 * *[LOG-CHECK-IN]* Must log every voter check-in.
 * *[LOG-CHECK-IN-OK]* Must log, for each checked-in voter who is permitted to
   vote, a record including the voter and the voter's ballot style.
 * *[LOG-CHECK-IN-WRONG-PP]* Must log, for each voter who is permitted to vote
   but not at the current polling place, a record including the voter and the
   voter's designated polling place.
 * *[LOG-CHECK-IN-NOT-PERMITTED]* Must log, for each voter who attempts to
   check in but is not permitted to vote, a record including the voter.
 * *[LOG-CHECK-IN-TOKEN]* Upon check-in of a voter who is permitted to vote in
   the current election, must give that voter a ballot style token.
 * *[LOG-EVIDENCE-SERVER]* Must send logs to the evidence server.
 * *[CHECK-IN-ONCE]* Must prevent a voter from checking in to vote more than
   once.
 * *[REGISTRATION-TEXTUAL-UI]* Must have an interactive user
   interface for voter authentication.
 * *[REGISTRATION-EVIDENCE-EXPORT]* Must have the ability to export
   check-in data to the Evidence Server.

### Optional

 * *[REGISTRATION-GUI]* May have an graphical interactive user
   interface for voter authentication.
 * *[PRINT-VOTER-LIST]* May be able to print out the current voter
   list at any point during the election.
 * *[PROVISIONAL-BALLOT]* May support process to supply provisional
   ballot.
 * *[PARALLEL-REGISTRATION]* May be able to authenticate and
   check in voters at multiple machines simultaneously in various
   venues across the jurisdiction.
 * *[LOG-REGISTRATION-PROCESSES]* May be able to log process or data
   inconsistencies.
 * *[REDIRECT-VOTERS]* May assist lost voters to find their designated
   polling places.

Non-functional requirements are as follows.

#### Usability

 * *[REGISTRATION-SIMPLE-UI]* The user interface should be simple to
   use for non-technical users (election representatives).
 * *[ARBITRARY-CHECK-IN]* The voter must be able to check in at any
   table at the voting venue.

#### Persistence

 * *[REGISTRATION-DATA-INTEGRITY-SYSTEM]* The system must exhibit no
   data loss from an arbitrary failure (e.g., a typical system failure
   like a OS crash) of any system in the *BVS 2020* network.
 * *[REGISTRATION-DATA-INTEGRITY-NETWORK]* The system must exhibit no
   data loss in the event of a network failure.

#### Scalability

 * *[REGISTRATION-SCALABILITY]* The system should be able to handle a
   large number of voters (approximately 10,000 voters in a single
   voting venue with 10 machines running the *BVS 2020*).

#### Security

 * *[REGISTRATION-SYSTEM-SECURE]* The system must use proper security
   measures and cryptography to establish confidence that the system
   is secure.
 * *[REGISTRATION-VOTER-LOOKUP]* The system should be able to filter
   voters in a voter list based on multiple criteria to determine
   eligible voters.
 * *[REGISTRATION-AUDIT-DATA]* The system must be able to provide
   sufficient audit information to allow the detection of suspicious
   voters and fraud.
 * *[REGISTRATION-REPORT]* The system should be able to provide a
   status report on the digital voter list prior to an election and
   afterwards.

#### Analysis:

 * *[REGISTRATION-VISUALIZE-TURNOUT]* The system should be able to
   visualize the turnout results.

## Documentation

@todo manifest of documentation for the subsystem

## Validation and Verification Methodology

Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

The properties that we will verify in the Registration
System are of three classes:
 1. data integrity
 2. data privacy
 3. voter check-in process properties
 
As such, we intend to model the dataflow and voting process in Cryptol
and ACSL and use Cryptol, SAW, and Frama-C to verify these properties.
Secrecy properties may relate to dataflow analysis depending upon
design choices we make, in which case either SSITH hardware or static
analysis about dataflow may be of use.

## Contributors

 - Reuben Broadfoot and Noah Rich wrote the first draft of this
   description.
 - Joe Kiniry, Dan Zimmerman, and Alexander Bakst edited that first draft.

## Funders

This project is funded by the Defense Advanced Research Projects Agency
(DARPA) under Contract No. HR0011-18-C-0013 (the Galois BESSPIN project). 
Any opinions, findings, and conclusions or recommendations expressed herein
are those of the contributors and do not necessarily reflect the views of DARPA.

The BVS 2020 cryptographic protocol and implementation are based upon the
Microsoft ElectionGuard SDK, funded by Microsoft and designed and developed by
Galois and Free & Fair.

