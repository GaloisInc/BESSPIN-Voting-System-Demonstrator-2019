# Registration System

## Executive Summary

A *Registration System* (also known as an *Electronic Pollbook*, or
*ePollbook* for short) that is used to facilitate the identification of
legal voters in a specific polling place or vote center.  Voters that
are permitted to vote are associated with a *Ballot Style*.  Voters that
are in the wrong polling place are redirected to their proper polling
place.  Voters that are not permitted to vote are turned away.  Each
of these kinds of transactions on voters is logged for the
authorities.  Voters are only permitted to vote once in an election.

## Overview

When a voter walks into the polling place to vote, the voter’s identity is 
validated against the voter registration database. After checking the voter’s 
identity against the registration system, one of several events may occur:

*  The voter is verified as a registered voter, checked off as having checked 
in, and provided an appropriate ballot style for voting.

*  The voter is not already registered in the registration system and provides 
evidence that he/she should be allowed to vote. In this case, the voter may be 
added to the registration system, checked off as having checked in, and provided
an appropriate ballot style for voting.

*  The voter is registered, but has already voted. In this case, the voter can 
either:

     *  Contest the status, in which case, the voter record should be flagged 
     for further investigation and the voter is redirected to an election 
     official.

     *  Confirm that he/she did already vote and subsequently exits the voting 
     process.

## Manifest

Code repository for the BVS 2020 https://gitlab-ext.galois.com/ssith/voting-system

## Glossary

https://github.com/FreeAndFair/ElectionGlossary/blob/master/Glossary.md

## Requirements

What follows are the mandatory and secondary requirements imposed upon the BVS 
2020 Registration System.  Informal verification (in the traditional software 
engineering sense) of these requirements is accomplished by several means, 
including formal verification of properties of the system's specification and 
implementation, as well as traceability from the requirements to artifacts that 
validate that they are satisfied (e.g., system tests, code review, etc.).

### Mandatory

* Must be able to generate voter cards from a given set of eligible voters
* Must be able to authenticate a voter based on a voter card number
* Must be able to record when a voter has been given a ballot and securely store
this information for posting voting history
* Must prevent a voter from being issued more than one ballot
* Must be able to authenticate and register voters at multiple machines 
simultaneously in various venues across the jurisdiction
* Must have an interactive user interface for authentication and registration
* Must be able to print out the current voter list at any point of the election

### Optional

####Usability:

* The user interface must be trivial to use for non-technical users (election 
representatives).
* The voter should be able to register at any table at the voting venue.

####Persistence:

* The system will exhibit no data loss from an arbitrary failure (e.g., a 
typical system failure like a Windows crash) of any system in the *BVS 2020* 
network.
* The system will exhibit no data loss in the event of a network failure.

####Scalability:

* The system should be able to handle a large number of voters (approximately 
30,000 voters in a single voting venue with 10 machines running the *BVS 2020*).

####Security:

* The system should use proper security measures and cryptography to establish 
confidence that the system is secure.
* The system should be able to filter voters in a voter list based on multiple 
criteria to determine eligible voters.
* The system should be able to provide sufficient audit information to allow the
detection of suspicious voters and fraud.
* The system should be able to provide a status report on the digital voter list
prior to an election and afterwards.

####Analysis:

* The system should be able to provide an analysis of the turnout, both 
nationally and for specific turnout results.
* The system should have a public API for the media or any citizen to access 
(after the election).
* The system should be able to visualize the turnout results.
* The system should be able to print the list of eligible voters.

## Documentation

@todo manifest of documentation for the subsystem

## Validation and Verification Methodology

Our overall approach to system assurance is summarized in
[ASSURANCE.md](../ASSURANCE.md).

@todo summary of our approach for this particular subsystem, including
a manifest of related artifacts.

## Contributors

The BESSPIN Voting System project has the following contributors:

*  Joseph Kiniry, Galois Principal Scientist, BESSPIN Principal Investigator, 
Free & Fair CEO and Chief Scientist, and the main inventor of the system.
*  Daniel Zimmerman, Galois Principal Researcher, BESSPIN co-Principal 
Investigator, Free & Fair Computer Scientist
*  Joey Dodds, Galois Principal Researcher, ElectionGuard Scientific Lead, Free
& Fair Computer Scientist
* Noah Rich
* Jason Graalum
* Reuben Broadfoot
* Rod Chapman
* Alexander Bakst
* Dragan Stosic
* Michal Podhradsky
* Kenny Foner
* Giuliano Losa
* Steven Osborn
* Annie Cherkaev
* Luke Myers
* John Sebes
* Dan Wallach
* Shpatar Morina
* Parker Southwick
* Haneef Mubarak

@todo kiniry Add and update contributor list as we work this year. The above 
list is a dump from GitLab's reported contributors in no particular order.

## Funders

This project is funded by DARPA under the Galois BESSPIN project. The BVS 2020 
cryptographic protocol and implementation are based upon the Microsoft 
ElectionGuard SDK, funded by Microsoft and designed and developed by Galois and 
Free & Fair.
@todo kiniry Add appropriate verbiage here for DARPA attribution.

