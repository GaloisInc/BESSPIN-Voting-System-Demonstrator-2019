# Registration System

## Executive Summary

A *Registration System* (also known as an *Electronic Pollbook*, or
*ePollbook* for short) is used to facilitate the identification of
legal voters in a specific polling place or vote center.  Voters that
are permitted to vote are associated with a *Ballot Style*.  Voters
that are in the wrong polling place are redirected to their proper
polling place.  Voters that are not permitted to vote are turned away.
Each of these kinds of transactions on voters is logged for the
authorities.  Voters are only permitted to vote once in an election.

## Overview

When a voter walks into the polling place to vote, the voter’s
identity is validated against the voter registration database, which
is contained in the Registration System.  After an election official
checks the voter’s identity against the registration system, one
of several events may occur:

* the voter is verified as a registered voter, persistently recorded
  as having checked-in, and provided an appropriate ballot style for
  voting,

* the voter is not already registered in the registration system and
  provides evidence that he/she should be allowed to vote. In this
  case, the voter may be added to the registration system,
  persistently record as having checked-in, and provided an
  appropriate ballot style for voting.

* the voter is registered, but has already voted. In this case, the
  voter can either:

     * contest the claim that they have already checked-in, in which
       case, the voter record should be flagged for further
       investigation and the voter is redirected to an election
       official.

     * confirm that he/she did already vote and subsequently exits the
       voting process.

## Manifest

- [Code repository for the BVS 2020](https://gitlab-ext.galois.com/ssith/voting-system)

## Glossary

Our system glossary is based upon the 
[Free & Fair Election Glossary](https://github.com/FreeAndFair/ElectionGlossary), 
which is in turn based upon the 
[NIST Election Glossary](https://pages.nist.gov/ElectionGlossary/).

## Requirements

What follows are the mandatory and secondary requirements imposed upon
the BVS 2020 Registration System.  Informal verification (in the
traditional software engineering sense) of these requirements is
accomplished by several means, including formal verification of
properties of the system's specification and implementation, as well
as traceability from the requirements to artifacts that validate that
they are satisfied (e.g., system tests, code review, etc.).

Mandatory requirements use the modal verb _must_; optional
requirements use the modal verb _shall_ or _should_.

Our top-level requirements are as follows.

### Mandatory

 * *[AUTHENTICATE_VOTER]* Must be able to authenticate a voter.
 * *[VOTER_STYLE]* Must identify the correct ballot style for the
   voter.
 * *[UNKNOWN-UNDER-DISCUSSION]* Must be able to provide evidence of
   registration and ballot style.
 * *[CHECK-IN-ONCE]* Must prevent a voter from checking-in to vote
   more than once.
 * *[REGISTRATION-TEXTUAL-UI]* Must have an textual interactive user
   interface for voter authentication.
 * *[REGISTRATION-EVIDENCE-EXPORT]* Must have the ability to export
   check-in data to the Evidence Server.

### Optional

 * *[REGISTRATION-GUI]* Shall have an graphical interactive user
   interface for voter authentication.
 * *[PRINT-VOTER-LIST]* Shall be able to print out the current voter
   list at any point of the election.
 * *[PROVISIONAL-BALLOT]* Shall support process to supply provisional
   ballot.
 * *[PARALLEL-REGISTRATION]* Shall be able to authenticate and
   check-in voters at multiple machines simultaneously in various
   venues across the jurisdiction.
 * *[LOG-REGISTRATION-PROCESSES]* Shall be able to log process or data
   inconsistencies.
 * *[REDIRECT-VOTERS]* Shall assist lost voter to find their precinct.

Non-functional requirements are as follows.

#### Usability

 * *[REGISTRATION-SIMPLE-UI]* The user interface should be simple to
   use for non-technical users (election representatives).
 * *[ARBITRARY-CHECK-IN]* The voter should be able to check-in at any
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
 * *[REGISTRATION-AUDIT-DATA]* The system should be able to provide
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

The properties that we will be verifying in the Registration
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
 - Joe Kiniry edited that first draft.

## Funders

This project is funded by DARPA under the Galois BESSPIN project. The
BVS 2020 cryptographic protocol and implementation are based upon the
Microsoft ElectionGuard SDK, funded by Microsoft and designed and
developed by Galois and Free & Fair.

@todo kiniry Add appropriate verbiage here for DARPA attribution.

