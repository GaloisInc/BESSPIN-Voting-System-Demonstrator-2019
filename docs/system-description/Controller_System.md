# Controller System

## Executive Summary

A *Controller System*, which coordinates the running of an election in
a single polling place.  The Controller System permits an EO to spoil
ballots that voters deem incorrectly filled out or otherwise damaged.
As a part of that workflow—as well as a part of the E2E-V challenge
discussed later—this system also facilitates the issuance of new
ballot style tokens so that a voter can start over and obtain a new
unmarked paper ballot.

## Overview

Once a voter has been authorized to vote in an election, the voter is issued a
Ballot Style token which is exchanged for exactly one ballot. As part of the E2E
voting protocol, the voter may do one of several things with this ballot.

1. The voter may mark her choices and cast the ballot.

2. The voter may mark her choices using a BMD, realize an error has been made in
   recording her choices, and receive a new ballot to replace the
   previous, incorrectly-marked ballot.

3. The voter may mark her choices and decide to produce a _challenge_ ballot
   record. In this case, the voter receives a new ballot to replace the
   previous, challenged ballot.
   
In scenarios 2 and 3, the voter is entitled to ballots beyond the initial ballot.

The *Controller System* is responsible for issuing new Ballot Style tokens to
voters. In particular, it allows _election officials_ to spoil ballots on behalf
of voters, and issue new BS tokens in exchange for a spoiled ballot. Hence, the
controller system is responsible for spoiling ballots in addition to issuing
Ballot Style tokens.

@todo abakst Not sure about the above bit, but it seems to me that the CS should only
hand out a BS token if presented with a spoiled ballot. 

## Manifest

This subsystem's artifacts are found in the following locations:

- [Development Plan](../specs/lando/controller_system/plan.lando)
- _Documentation_: No documentation beyond this file exists at the moment.
- [Specification](../specs/lando/controller_system)
- _Source Code_: No source code exists at the moment.
- [Code repository for the BVS 2020](https://gitlab-ext.galois.com/ssith/voting-system)

The following issues track the design and development of this subsystem:

- _Development Plan_: #202
- _System Description_: #203
- _Threat Model_: #204
- _Domain Model_: #205

## Glossary

Our system glossary is based upon the 
[Free & Fair Election Glossary](https://github.com/FreeAndFair/ElectionGlossary), 
which is in turn based upon the 
[NIST Election Glossary](https://pages.nist.gov/ElectionGlossary/).

What follows are the mandatory and secondary requirements imposed upon
the BVS 2020 Controller System.  Informal verification (in the
traditional software engineering sense) of these requirements is
accomplished by several means, including formal verification of
properties of the system's specification and implementation, as well
as traceability from the requirements to artifacts that validate that
they are satisfied (e.g., system tests, code review, etc.).

Mandatory requirements use the modal verb _must_; optional
requirements use the modal verb _shall_ or _should_.

Our top-level requirements are as follows.

## Mandatory

* *[AUTHENTICATE_OFFICIAL]* Must be able to authenticate an election official.
* *[ACCESS_CONTROL]* Must restrict capability to spoil ballots and issue BS tokens to authenticated election officials.
* *[SPOIL_BALLOT]* Must allow election officials to spoil ballots.
* *[ISSUE_TOKEN]* Must issue exactly one BS token in exchange for a spoiled ballot.

## Contributors

* Alexander Bakst and Joe Kiniry contributed to the first draft of this description.
