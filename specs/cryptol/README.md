# Cryptol Specifications of the BESSPIN Voting System

*Joey Dodds, Joe Kiniry*

# Introduction and Purpose

This directory contains Cryptol specifications for portions of the
*BESSPIN Voting System* (BVS). We use Cryptol when we wish to
precisely specify a subsystem, including explaining, (at an abstract
level decoupled from implementation decisions), subsystem components,
data-types, and correctness properties.

Using such specifications Cryptol is used to make sure the subsystem
is: 
 - _simple_, _clean_ and _well-typed_,
 - _complete_ from the point of view of scenarios we wish for it to
   support, and
 - is formally _correct_ according to specified Cryptol _properties_,
   which are theorems about the model.

In addition to the above, Cryptol specifications are used for one or
more of the following purposes:
 - _runtime verify the model_ by executing tests at the model
   level, as Cryptol specifications are executable,
 - _validate the model_ by testing properties with automatic random
   testing,
 - _generate test vectors_ for the model and implementation, 
 - _inspire and help formulate an algebraic/axiomatic specification of
   the subsystem in ACSL_, and,
 - in tandem with SAW, _formally verify our C implementation against
   the Cryptol formal model_.

We rely upon open specifications of our underlying cryptographic
algorithms. These Cryptol specifications are found in the
[cryptol-specs project](https://github.com/GaloisInc/cryptol-specs)
hosted at GitHub. In particular, specifications for AES are SHA-2
found therein now, and we will add any other algorithms we need there
soon, such as CBC-MAC.

# Subsystem Specifications

Four main subsystems are specified here using Cryptol.

1. The cryptographic *Ballot Protocol* used by the *Ballot Marking
   Device* (BMD) and the *Smart Ballot Box* (SBB) to communicate voter
   choices encoded in barcodes on paper ballots. This protocol
   includes both the encoding of voter choices as well as the wire
   format for communication.
2. The cryptographic *Log Protocol* used by the *Logging* subsystem to
   log critical system hardware and application-level events.
3. The underlying cryptographic algorithms used by these two
   cryptographic protocols, such as AES and SHA-2.  These are a part
   of the *Crypto* subsystem.
4. The Abstract State Machine (ASM) for the *Smart Ballot Box*.


