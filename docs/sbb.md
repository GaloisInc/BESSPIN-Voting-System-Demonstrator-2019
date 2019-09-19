# The BVS 2020 Smart Ballot Box


## Introduction

<!-
SLO: Previous text (pulled from system description) stated that the 
SBB primary purpose was to determine if a ballot is legal for
the current election. I have changed this to reflect that that
determination is made by the controller.
-->

The Smart Ballot Box or SBB is a subsystem of the 2020 BVS which
permits a voter to securely store a legal, marked paper ballot.
The main function of the SBB is to accept and store a legal ballot
for the current election and to reject ballots that are not part of
the current election.


## Description

When a voter is ready to cast their vote they may insert their marked
ballot into the SBB. The ballot is then held in a temporary location
out of physical reach.

The SBB scans a 1D/2D barcode located on the paper ballot and the
barcode (containing nonidentifiable information) is forwarded
to the controller. The controller makes a determination regarding the
validity of the ballot, taking into consideration the timeliness,
uniqueness, and correctness of the ballot and returns that result to
the SBB.

If the controller rejects the ballot, the ballot will be ejected
from the paper feeder, the reason for rejection will be logged by
the logging subsystem and an error message displayed to the voter.

<!-
SLO: This paragraph is all assumptions on my part.
-->

If a local network error, controller error, or time window expires,
resulting in an unexpected condition the SBB will eject the
ballot. The SBB will then report the error to the logging subsystem
and display a message to the voter.  Once connectivity to the 
controller is restored the ballot may be recast as long as the ballot
has not expired.

If the ballot is determined by the controller to be correct and 
countable for the current election the voter will be prompted via
the SBB UI to either cast or spoil their vote.

Casting is done via voter button press and triggers the SBB paper
feeder to advance the ballot completely into the SBB secure container
where it is stored until the end of the election.  Once a ballot is 
cast, a duplicate ballot with the same barcode will be rejected by 
any SBB communicating with the controller for that election.

<!-
SLO: Should there be an exception for ballot-boxes that are full and
may be emptied mid election.  If so is there any concerns we should
have regarding state kept on the SBB or controller.
-->

A voter may also choose to spoil their vote because of a marking error
or change of heart.  They may also choose to spoil their vote as a
method of challenging the voting terminal.  A spoiled vote is recorded
as such and the ballot ejected from the SBB. A spoiled may not be
recast.

The SBB allows officials and voters to challenge the BVS by trying to
cast an invalid ballot which would be rejected or inserting a valid
test ballot which may be spoiled, thus not tabulating the test ballot
result as part of the election.

All ballot actions, external events, as well as internal device
state-machine changes are communicated to the logging subsystem and
may be stored in the evidence server for verifiability.

## Mechanical design goals

The primary design goals for the SBB are security, accuracy,
modular design, and cost efficiency.

The modular design will provide an integrated paper feeder, screen, 
and user interface that can be attached to various existing ballot
boxes and secure containers.

For BVS 2020 the SBB will be tethered to and driven by government
furnished equipment aka GFE running one of the TA1 teams secure P1 
processors.  However, the SBB modular design will allow other secure 
processors including (but not limited to) the CASCADES FPGA platform.
To be attached and potentially integrated into the SBB and not
tethered externally.

## Components
* Barcode scanner
* Paper feeder
  * Motor (Forward / Reverse)
  * Paper detection
* User Interface
  * Spoil / Cast buttons
  * User prompt / LCD display
* Secure container

## Subsystem dependencies
  * crypto
  * logging
  * security

