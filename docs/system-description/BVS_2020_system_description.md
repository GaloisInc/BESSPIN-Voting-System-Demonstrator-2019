# BVS 2020 System Description

# Introduction

The main system that is being implemented is the BESSPIN Voting
System, or BVS for short.

The BVS is an End-to-End Verifiable (E2E-V) Voting System.  It is a
networked computing system composed of several distinct subsystems.
Each subsystem is a Ethernet-networked computing element.  Not all
subsystems are on the same network.  A future network specification will
detail the means by which subsystems are networked.  All
subsystems are implemented in C, and depend only upon libraries and
operating systems implemented in C, so as to best leverage SSITH TA-1
team secure compilers.

All implementations must be designed and implemented with the goals of
SSITH in mind, particularly with regards to demonstrating secure
hardware capabilities and the precise concretization of CWEs in the
program.

Some of the subsystems are deemed *Core Subsystems* and are
consequently part of the red team exercise in DEF CON 2020 and beyond.
Others are *Supplemental Subsystems*, and are thus necessary for the
overall functioning of the BVS, but will be deployed on COTS hardware,
much like was done for the BMD in DEF CON 2019.  Subsystems enumerated
below are labeled (*Core*) or (*Supplemental*) to briefly indicate in which
class they belong.  Those subsystems which are not mandated by the SSITH
SOW and are thus low priority and will be implemented only with IR&D funding
are labeled (*IR&D*).

As such, each core subsystem is cross-compiled by either the
off-the-shelf program supported LLVM (available via the BESSPIN Tool
Suite) or the secure compiler provided by each TA-1 team.  Each core
subsystem executed on a cross-compiled operating system on a TA-1
team’s SSITH SoC.

As at DEF CON 2019, the Smart Ballot Box runs on FreeRTOS on the RV32
(P1) CPU.  The Registration System, Controller System, BMD, and Paper
Ballot Scanner subsystems run on Linux or FreeBSD on the RV64 (P2)
CPU.  The Evidence Server runs on Linux or FreeBSD on the RV64 (P3)
CPU, if available, and, for those teams that only have a P2 available,
on that CPU instead.

# System Description Components

The BVS 2020 *System Description* is made up of:

- for the entire top-level BVS 2020 System, as well as for every
  subsystem thereof:
   - its refined project plan
   - its top-level system description
   - its domain model

## Project Plan

The BVS 2020 Project Plan is located in an OmniPlan plan called the
`BVS 2020 Project Plan`.

@todo kiniry Add the project plan and/or its export to this repo.

The main components of this plan to summarize here are system and
subsystems *owners*, the project *milestone schedule*, and the project
*release plan*.

@todo kiniry Write up these components.

## Subsystems Description

The BVS consists of the following subsystems:

1. (*Core*) A *Registration System* (also known as an Electronic Pollbook, or
   ePollbook for short) that is used to facilitate the identification
   of legal voters in a specific polling place or vote center.  Voters
   that are permitted to vote are associated with a Ballot Style.
   Voters that are in the wrong polling place are redirected to their
   proper polling place.  Voters that are not permitted to vote are
   turned away.  Each of these kinds of transactions on voters is
   logged for the authorities.  Voters are only permitted to vote once
   in an election.

2. (*IR&D*) A *Ballot Printer System* relates a ballot style to an
   Unmarked Paper Ballot.  The unmarked paper ballot acts as the activation
   token for a BMD.

3. (*Core*) A *Voting Terminal* (also known as a Ballot Marking Device, or BMD
   for short), which facilitates voters with disabilities to
   independently completely mark to their satisfaction in an accurate,
   voter-verifiable fashion, their unmarked paper ballot.  Voters who
   choose to complete their ballot by hand create what is known as a
   Hand-Marked Paper Ballot (HMPB) and do not use the BMD.  The BMD
   does not store any information about voters or their choices.

4. (*IR&D*) A *Voter Verification Device*, which facilitates voters of all kinds
   to verify that the ballot that they have completed (either by-hand
   or using the BMD) does, in fact, represent their wishes.  Voters
   who find an error in their ballot of their own doing go to the
   Election Official (EO) manning the Controller System (described
   below).  Voters who detect an error in the operation of a BMD
   report such to the Head EO of the polling place.  The Voter
   Verification Device runs on COTS hardware and software.

5. (*Core*) A *Controller System*, which coordinates the running of an election
   in a single polling place.  The Controller System permits an EO to
   spoil ballots that voters deem incorrectly filled out or otherwise
   damaged.  As a part of that workflow—as well as a part of the E2E-V
   challenge discussed later—this system also facilitates the issuance
   of new ballot style tokens so that a voter can start over and
   obtain a new unmarked paper ballot (step 2 above).

6. (*Core*) A *Ballot Scanning Device* (also known as a *Paper Ballot Scanner*,
   or *PBS* for short), which converts a paper ballot into a Cast Vote
   Record—a digital representation of the paper ballot’s contents (the
   voter’s selections).  The PBS can determine based upon such an
   interpretation if a ballot is incompletely or improperly marked and
   (optionally) provide the voter feedback on such (it can detect
   undervotes and overvotes and difficult-to-interpret ballots)[^1].

[1] A digital scanner of any kind can be used at this step or
post-election to scan every paper ballot into digital images (e.g.,
PNG files).  One can do so for each and every ballot observed (if at
step 6) or cast (if done post-election when SBB’s are emptied),
depending upon the kind of evidence one wishes to preserve and share
about the election via the Evidence Server.

   In the case of an E2E-V PBS, the PBS prints an E2E-V Ballot Receipt
   (aka a Vote Tracker, in ElectionGuard lingo).  Only after the
   tracker is in the voter’s hands does the PBS permit the voter to
   cast or spoil (aka an E2E-V challenge) their ballot.  In the latter
   case, the voter returns to the Controller System to obtain a new
   unmarked paper ballot.  In the former case, the voter takes their
   digitally cast ballot to the Smart Ballot Box.

7. (*Core*) A *Smart Ballot Box* (SBB), which permits a voter to
   securely store a legal, marked paper ballot. The main function of
   the SBB is to accept and store a legal ballot for the current
   election and reject ballots that are not part of the current
   election.

8. (*Core*) An *Evidence Server* (ES) (also known as a Bulletin Board in the
   E2E-V literature) shares all evidence of an election to the public
   using open common data, machine readable, formats.

   For a traditional voting system, the ES publishes the results of
   the election and public metadata on the election, such as the time
   and date of the election, the EOs responsible for the election, all
   of the ballot styles of the election, example blank ballot images
   for every style, total number of voters checked in, total number of
   ballots cast and counted, under/overcounts per contest, etc.

   For an E2E-V voting system, the ES also publishes the cryptographic
   evidence of the election so that independent third parties can both
   double-check the announced results of the election (via independent
   tabulation) and verify the election’s evidence (via E2E-V
   verification).  The ES also facilitates the lookup of a ballot
   receipt in an election’s evidence, so as to prove to a voter that
   the encryption performed by the PBS was, in fact, accurate.

9. (*Supplemental*) A *Tabulation Device*, which computes the outcome(s) of an election
   from the Cast Vote Records component of an election’s evidence.
   For a traditional election, such a tabulation is performed on
   cleartext data, preferably in the simplest means possible, and is
   double-checked through external tabulation of the same data (say,
   using a spreadsheet).  For an E2E-V voting system, tabulation is
   accomplished either via a decryption step (in the case of many
   mixnet-based systems) or via homomorphic tabulation (as is the case
   with ElectionGuard).

10. (*Supplemental*) In the case of an E2E-V Voting System, at least one *Verifier*,
    which consumes the cryptographic evidence of an election published
    on the ES and determine whether or not that evidence is
    well-formed.

11. (*Supplemental*) In order to support the use of SHIELD-based Verifiable Paper (VP)
    in the BVS 2020 system, we must develop a *SHIELD VP Server* (VPS),
    capable of managing and authenticating dielets affixed to
    verifiable paper in accordance with the BVS Protocol, discussed
    in `protocol.md`.

# Top-level System Requirements

The BVS 2020 system's requirements is driven by two main external sources: (1) our SOW
with Galois and hence DARPA, and (2) the draft VVSG 2.0 federal requirements on
voting systems (currently only in the form of principles via "Voluntary Voting
System Guidelines 2.0: Principles and Guidelines").

Thus, BVS 2020's mandatory requirements are derived from (1), and our supplementary
requirements are derived from (2).  The full text for (1) is located in the file
`SOW.md`.  The full text of (2) is located in the file `VVSG_2.0.md`.

@todo kiniry `SOW.md` will be added once the contract is signed with Galois.

@todo kiniry `VVSG_2.0.md` will come from [the VVSG website at the EAC](https://www.eac.gov/voting-equipment/voluntary-voting-system-guidelines/).

Additional mandatory system requirements that are not derived from these sources
are as follows:
 - *[SBB_Platform]* The SBB platform is any of the GFE P1s running the GFE FreeRTOS
   and using the CASCADIO I/O board or its successor to interface with SBB-specific
   I/O and storage devices.
 - *[SSITH_Platform]* All subsystems that target a SSITH platform must run on
   a GFE P2 or P3 (in the case of the *Evidence Server*).
 - *[COTS_Platform]* All subsystems that do not target a SSITH platform must run
   on an easily procurable COTS platform running a commonly available Linux
   distribution which also supports RISC-V.
 - *[BVS_PL]* All BVS implementations and their C-based dependencies, within reason,
   must be written in verifiable C that can be successfully compiled with the GFE's LLVM.
 - *[LLVM_Compilation]* All implementations and their dependencies, within reason,
   must be compiled with the GFE's LLVM or a TA-1 team's fork thereof.
 - *[CASCADES]* The CASCADES platform must run the SBB subsystem.

 # Contributors

The BESSPIN Voting System project has the following contributors:
 - Joseph Kiniry, Galois Principal Scientist, BESSPIN Principal Investigator,
   Free & Fair CEO and Chief Scientist, and the main inventor of the system.
 - Daniel Zimmerman, Galois Principal Researcher, BESSPIN co-Principal
   Investigator, Free & Fair Computer Scientist
 - Joey Dodds, Galois Principal Researcher, ElectionGuard Scientific Lead,
   Free & Fair Computer Scientist
 - Noah Rich
 - Jason Graalum
 - Reuben Broadfoot
 - Rod Chapman
 - Alexander Bakst
 - Dragan Stosic
 - Michal Podhradsky
 - Kenny Foner
 - Giuliano Losa
 - Steven Osborn
 - Annie Cherkaev
 - Luke Myers
 - John Sebes
 - Dan Wallach
 - Shpatar Morina
 - Parker Southwick
 - Haneef Mubarak

@todo kiniry Add and update contributor list as we work this year.  The above list
is a dump from GitLab's reported contributors in no particular order.

# Funding

This project is funded by DARPA under the Galois BESSPIN project.
The BVS 2020 cryptographic protocol and implementation are based upon
the Microsoft ElectionGuard SDK, funded by Microsoft and designed and
developed by Galois and Free & Fair.

@todo kiniry Add appropriate verbiage here for DARPA attribution.


