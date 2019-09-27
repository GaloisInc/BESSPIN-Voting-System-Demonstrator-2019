# Tabulation Device

## Executive Summary

A *Tabulation Device* computes the outcome(s) of an election from the
*Cast Vote Records* component of an election’s evidence.

## Overview

For a traditional election, tabulation is performed on cleartext
data, preferably in the simplest means possible, and is double-checked
through external tabulation of the same data (say, using a
spreadsheet).

For an E2E-V voting system, tabulation is accomplished
either via a decryption step (in the case of many mixnet-based
systems) or via homomorphic tabulation (as is the case with
ElectionGuard).

In both settings, a tabulator is nothing more than a (usually deterministic)
function that takes a set of CVRs and produces a total of all votes for all
contests.

Election statutes and sometimes rules dictate how one tabulates a set of
ballots, often by explaining how one tabulates votes in a single race.
Thus, a tabulator is a computational algorithmic translation of those
statutes and rules into code or processes.  Tabulation is a process in the 
case that the tabulator is one or more human beings performing a hand-count.

Formally verified tabulators have been created to realize several (often very 
complex voting) methods.  Many of these tabulators were created by Joe Kiniry's 
research group when he was a professor.  These include the Netherlands 
list-based method, Denmark's single-selection method, and Ireland's 
Proportional-Representation through Single Transferable
Vote (PR-STV) method.  Free & Fair has created two high-assurance tabulators,
one for San Francisco's Rank Choice Voting (RCV) method and the other for
homomorphic tabulation of plurality method ballots in ElectionGuard.

@todo kiniry Add links to all of the above projects.

## Manifest

@todo an itemized list or table indicating where to find more information

## Glossary

@todo point to the BVS 2020 and Free & Fair glossaries

## Requirements

Given that we are implementing a traditional and an E2E-V voting system in 
BVS 2020, we need two tabulators: one that can tabulate plaintext CVRs, and
one that can homomorphically tabulate enciphered CVRs.  The latter is included
with ElectionGuard.

### Mandatory

- *[PLAINTEXT_TABUATION]* Description.
- *[HOMOMORPHIC_TABULATION]* Description.
- *[PLURALITY_METHOD]* Description.
- *[TABULATION_CDF]* Description.
- *[WRITE-INS]* Description.
- *[]* Description.
- *[]* Description.

### Optional

- *[RCV_METHOD]* Description.

## Documentation

@todo manifest of documentation for the subsystem

## Validation and Verification Methodology

Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

@todo summary of our approach for this particular subsystem, including
a manifest of related artifacts.

## Contributors

- Joe Kiniry wrote this subsystem description.

## Funders

@todo indicate DARPA's support and indicate if any other agencies
contributed resources