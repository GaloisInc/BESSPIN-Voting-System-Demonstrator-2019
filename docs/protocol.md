# The BVS 2020 Protocols

## Overview

All subsystems communicate with each other via the BVS Protocol.  The
BVS protocol has, as its communication elements, digital (packets) and
physical (tokens) mechanisms.  Principals in the protocol include
computational elements (the computers which run subsystem
implementations) and people who use or manage the BVS system and its
subsystems.

The foundational principals and the high-level protocol realized by
the BVS is described in the original proposal submitted to DARPA.  The
BVS product comes in two variants: (1) a traditional voting system
variant that resembles today’s certified voting systems, and (2) an
end-to-end verifiable variant that is based upon the ElectionGuard
protocol and SDK.

The BVS 2020 Protocol is precisely specified here in natural language.
We use this specification as a means by which to ensure that all *events*
of the system that are realized by protocol actions are included in the
full set of events specified in the BVS 2020 system.  *Events* in our
system specification language can be thought of as, when viewed from the
outside of a subsystem, atomic interactions with a subsystem that
are either *inbound* or *outbound* (*in* and *out* events, respectively).

Examples of concrete realizations of events include:
 - explicit calls to a function or method invocation
 - implicit callbacks to functions bound via closure, UI event frameworks, etc.
 - packets or messages being sent or received on a network socket
 - HTTP RESTful messages being sent or received on a network interface
 - streams of bytes being sent or received via a file descriptor
 - keyboard or mouse input
 - UI updates

## Our Principals

The *human principals* in the BVS 2020 protocol are as follows:

1. An *Election Commission* made up of one or more *Commissioners*.
2. Each election has one or more *Trustees*.
3. A Polling Place *Supervisor* who is responsible for a *Polling
   Place* by virtue of being responsible for the Polling Place
   *Controller*.
4. A Polling Place *Worker* who is in the role of a *Voter
   Authenticator* and thus is responsible for a *Registration System*.
5. A Polling Place Worker who is an *Election Assistant* responsible
   for helping voters who have trouble of any kind in the Polling
   Place.
6. Any other members of the *Public*.

The *network principals* in the BVS 2020 protocol are as follows:

1. A *Polling Place Network* is the sole network used by the BVS in a
   polling place. From a technical and security point of view, this
   network can either be a wired or wireless network.  From a federal
   requirements point of view (potentially, wrt VVSG 2.0), wireless
   communications may not be permitted. Likewise, STAR-Vote's RFP
   mandated only the use of Ethernet for network communications,
   primarily to address transparency-related concerns.
   
2. Several computational principals (enumerated below) must be air
   gapped and thus are not on any network at all. Preferably, these
   systems in a certified deployment would not even have the physical
   capability to communicate with the outside world over a physical or
   wireless network.

The *computational principals* in the BVS 2020 protocol are as
follows.  Each of these is summarized in the `BVS 2020 system
description.md`. *Core* principals are mandatory and are the focus of
red team activities, according to our SOW with Galois and thus DARPA.
*Supplemental* principals are necessary to create the BVS 2020, but
are not subject to SSITH-centric red teaming and will run on COTS
systems.  *IR&D* principals are 

### Core Principals

1. *Registration Server* (*RS*)

2. *Voting Terminal* (aka a *Ballot Marking Device* or *BMD* for
   short)

3. *Controller System* (*CS*)

4. *Ballot Scanning Device* (aka *Paper Ballot Scanner* or *PBS* for
   short)

5. *Smart Ballot Box* (*SBB*)

6. *Evidence Server* (*ES*)

### Supplemental Principals

1. *Ballot Printer System* (*BPS*)

2. *Tabulation Device* (*TD*)

3. *Election Verifier* (*EV*)

4. *Verifiable Paper Server* (*VPS*)

### IR&D Principals

1. *Voter Verification Device* (*VVD*)

## The Protocol Summary

In our precise English description of the protocol that follows, we
use the following abbreviations.  These are included in a State Key
in our "BVS 2020 Dataflow Models" (Polling Place and Post-Election),
found in Drive.

B    := Ballot
BI   := Ballot Image
BMD  := Ballot Marking Device
BS   := Ballot Style
CB   := Cast Ballot
CE   := Current Election
CR   := Certified Result
CS   := Controller System
CVR  := Cast Vote Record
E    := Evidence
EA   := Election Assistant
EC   := Electoral Commission
L    := Logs
M    := Map of Polling Places
MP   := Member of the Public
PBS  := Paper Ballot Scanner
PK   := Privacy Kiosk
PP   := Polling Place
PR   := Provisional Result
R    := Receipt
RS   := Registration Server
RV   := Registered Voters
S    := Supervisor
SB   := Spoiled Ballot
V    := Voter
VA   := Voter Authenticator
VPII := Voter V’s PII
VVD  := Voter Verification Device
XB   := Challenged Ballot

Each protocol description is a set of sequences of labeled steps.
Several different subprotocols exist: one for the pre-election key
ceremony, one for election day in the polling place, and three for
post-election activities.  Each step in the protocol takes place at a
partcular device, sometimes with an election official assisting or
otherwise interacting with the voter.

### Pre-Election Key Ceremony

We intend to use the ElectionGuard pre-election key ceremony.  We intend to
use COTS HSMs (such as Yubikeys or Titan keys) in order to generate and store 
keys as a part of the Shamir election setup subprotocol.

### Election Day

1. *VoterCheckIn* A voter V arrives at a polling place PP to check in
   for election CE.
   The RS has a relation between all voters in RV and all polling
   places in CE.  The VA responsible for the RS checks V's VPII to
   determine if they are permitted to vote or not. Regardless of the
   results of this check, all such checks are logged. Each voter in RV
   can only transition from an unregistered to a registered voter
   exactly once, so as to only be handed a single ballot at the BPS.

1.a. If the voter V is permitted to vote in CE at PP, then they are
     given a *BS Token* that represents their BS and they go to the
     Ballot Printer Station.

1.b. If the voter V is permitted to vote in CE, but not at PP, then
   they are given a map M for all polling places for CE and are
   redirected to the right polling place.

1.c. If the voter V is not permitted to vote in CE, they are turned
   away.

// @todo kiniry As a part of the procedural and data audit the list of
// voters turned away must be reported to the EC for investigation.

// @design kiniry Determine what the BS token should be.

2. *Ballot Printing* The BPS, on consuming the anonymous BS Token,
   produces an unmarked paper Ballot B which V takes.
   
2.a. Ballots can either be printed on-demand (what is called a
     Ballot-on-Demand system) or, with a sufficiently small set of
     BSs, we can pre-print ballots.

2.b. Voter V decides if they wish to vote using an assistive Ballot
     Marking Device (BMD), aka a Voting Terminal

// @design kiniry Should all ballots of a given BS be identical?

3.a. *Voting Terminal* Voter V decides to vote on B using random,
     voter-chosen BMD<sub>i</sub>.

     Blank ballot B indicates to BMD<sub>i</sub> which BS it
     encodes. The BMD facilitates V's independent voting using B,
     producing at the end of the voting session, a Marked Ballot B'.

3.b. *Privacy Kiosk* Voter V decides to vote on B using a pen in
     Privacy Kiosk PK.

     Voter V independently produces a (Hand) Marked Ballot B'.

// @design kiniry Should images of all spoiled ballots part of E?

4. *Voter Verification Device* Voter V takes B' to random,
   voter-chosen VVD<sub>j</sub> and uses VVD<sub>j</sub> to confirm
   that B' captures their casting intentions.

4.a. If V determines that B' does not capture their intentions and
     they used BMD<sub>i</sub>, they report to the Supervisor a
     problem with BMD<sub>i</sub>.  B' is spoiled and kept by S for
     investigation and auditing purposes.

     V is then escorted to the *Controller System* CS where they are
     given a new BS Token, an they return to step 2 above.

4.b. If V determines that B' does not capture their intentions and
     they do not believe that, if they used a BMD, it acted
     improperly, then they go to the Polling Place's *Controller
     System*, which is managed by the Supervisor S, to spoil their
     ballot and start over. Go to step 5.

4.c. If V determines that B' does capture their intentions, or they do
     not care to double-check their ballot, then they go to the
     random, voter-chosen *Ballot Scanning Device* (a *Paper Ballot
     Scanner*, PBS<sub>k</sub>) to cast or challenge their vote. Go to
     step 6.

5. *Controller Device* V spoils their ballot and starts over.

   Voter V interacts with Supervisor S responsible for the Polling
   Place Controller Server CS.  S spoils voter V's ballot B, and keeps
   the spoiled ballot SB for auditing purposes.  S gives V a new BS
   Token and V returns to the BPS.  Go to step 2.

6. *Ballot Scanning Device* V inserts B into PBS<sub>k</sub> and the
   PBS determines if B is a legal ballot. If B is not a legal ballot,
   it is rejected, otherwise B is a legal ballot, and B is interpreted
   into a CVR, the PBS commits to that interpretation and emits a
   receipt R, and the voter V is asked if he or she wishes to *cast*
   or *challenge* the device.

6.a. *Challenge* If V challenges the PBS, then B is cryptographically
     spoiled and returned to the voter and they are told to return to
     CS. There, they show their spoiled ballot B and receipt R to S
     and obtain a new BS Token, and V returns to the BPS.  Go to step
     2.

6.b. *Cast* If V chooses to cast B, then B is returned to them and
     they are told to insert B into a random, voter-chosen *Smart
     Ballot Box* (SBB).

7. *Smart Ballot Box* V inserts cryptographically cast ballot B into
   their chosen SBB. If B is a legal, cryptographically cast ballot
   for the election, it is accepted by SBB and stored securely for
   tabulation and auditing, otherwise B is rejected.

7.a. *Rejected Cast Ballot* If V insists that B is a cryptographically
     cast ballot, they may return to the CS for an investigation. This
     should never happen.

7.b. *Rejected Ballot* If V attempts to cast an irregular ballot B,
     then it is either not a ballot, is a tampered ballot, is a
     spoiled ballot, is a challenged ballot, or is an uncast ballot.
     In the latter case, the voter is sent back to the PBS; go to step
     6.  For all other cases, an EA will assist the voter.

### Post-Election Protocols

There are three different-but-interacting protocols used to conclude and 
audit an election.  

One part of concluding an election is closing the polls and collecting all
cast and spoiled ballots for tabulation and auditing.  The evidence generated
during an election is also collected for post-election processing.  That
evidence in our protocol is the cryptographic aggregation of all secure
logs from all devices, and the data therein includes a CVR and ballot image
for every cast or cryptographically spoiled ballot.

### Post-Election Subprotocol: Concluding an Election

Election officials main focus in concluding an election is first, tabulating the
cast ballots and, second, auditing the election and its evidence.  

The *Tabulation Device* consumes the CVRs and ballot images and produces a
tabulation, which is reported by the Electoral Commission as a *Provisional 
Result*.  A wise Electoral Commission will use several independently developed
tabulator concurrently to confirm results.

Next, election officials export *Evidence* from the *Evidence Server*. They use
that evidence to both (a) perform one or more *cryptographic verifications* of 
the evidence and (b) conduct a Risk-Limiting Audit.  

If both these verifications and RLA confirm the Provisional Result,
and officials' audits of other election artifacts show that the election was 
well-run and sound, then the Electoral Commission declares a *Certified
Result* that agrees with the Provisional Result.  

If the RLA fails, then either:
 - a forensic examination of the evidence and voting devices is necessary in the
   case of evidence of fraud, a security event, or otherwise, or
 - a manual hand-count is necessary because the election is too close to call
   with the evidence on-hand and electoral statue dictates how provisional and
   certified results are arrived at.

### Post-Election Subprotocol: Third Party Verification

Third parties, such as arbitrary members of the public, representatives from
participating political parties, the media, NGOs, etc. can perform independent
cryptographic verifications.  Third parties can download *evidence* from the
*Evidence Server* and check that evidence with an *Election Verifier*.

An *Election Verifier* consumes evidence and produces a report about that 
evidence.  A report either confirms that the evidence is cryptographically
well-formed, or reports on warnings and errors about the evidence.

Third parties can also use one or more independent *Tabulator*s to consume
evidence and produce their own *Third-Party Result*.

If any third party's verification fails or tabulation does not match the
Provisional Result reported by the Electoral Commission, they notify the
authorities and an investigation ensues.

@todo kiniry An unspecified protocol will be used by third parties to share 
their evaluation of the evidence, including their independent tabulations.

### Post-Election Subprotocol: Voter Verification

Each voter that participated in the election, or any other member of the public
who is given evidence artifacts from voters, can conduct a *voter verification*
as well.  Voter verification focuses on the cryptographic evaluation of cast
and spoiled ballot receipts.  Voters or their proxies interact with the 
Evidence Server in order to look up their receipt information.

Any of the following circumstances has a voter report to the Electoral 
Authorities a voter verification failure:
 - a spoiled ballot receipt is not verifiable
 - a spoiled ballot is not found in the evidence
 - a spoiled ballot's contents do not match the decrypted ballot information
   that is found in the evidence
 - a cast ballot's receipt is not verifiable

@todo kiniry If all of a voter's receipts are verifiable and their spoiled 
ballots contents match the evidence, then the use an unspecified protocol to 
report to the public their evalution of the evidence.

Voters can, of course, use the previous subprotocol and perform their own
independent cryptographic verification of the entire election's evidence and
perform their own tabulation.