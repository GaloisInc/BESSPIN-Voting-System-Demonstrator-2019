# Evidence Server

## Executive Summary

An *Evidence Server* (ES) (also known as a *Bulletin Board* in the E2E-V
literature) shares all evidence of an election to the public using
open common data, machine readable, formats.

For a traditional voting system, the ES publishes the results of the
election and public metadata on the election, such as the time and
date of the election, the EOs responsible for the election, all of the
ballot styles of the election, example blank ballot images for every
style, total number of voters checked in, total number of ballots cast
and counted, under/overcounts per contest, etc.

For an E2E-V voting system, the ES also publishes the cryptographic
evidence of the election so that independent third parties can both
double-check the announced results of the election (via independent
tabulation) and verify the election’s evidence (via E2E-V
verification).  The ES also facilitates the lookup of a ballot receipt
in an election’s evidence, so as to prove to a voter that the
encryption performed by the PBS was, in fact, accurate.