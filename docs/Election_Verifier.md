# Election Verifier

## Executive Summary

An *Election Verifier* consumes the cryptographic evidence of an
election published on the *Evidence Server* and determines whether or
not that evidence is well-formed.

## Overview

Any end-to-end verifiable cryptographic protocol creates cryptographic
evidence.  This evidence can/should be verified by a cryptographic
*Election Verifier* (or just "Verifier", for short).  

A verifier checks a set of formally specified properties in the
evidence; correctness and security properties that are meant to
demonstrate that the evidence is well-formed and proves that the
election is correct and secure.

Some of those properties and simple and focus on well-formedness
criteria of the evidence.  (Is the evidence complete?  Is it
well-typed?).  Other properties focus on basic security properties of
the evidence.  (Does the evidence have the appropriate cryptographic
provenance?  Is the evidence and all of its units signed by the
appropriate keys?  Is the hash chain in ever evidence log
well-formed?)  Advanced properties check security claims embedded in
the evidence.  (Is each piece of evidence rooted in a valid secure
boot?  Are all zero knowledge proofs well-formed?)

A verifier processing evidence has two possible outcomes:
 1. It might discover that the evidence is correct and reports such.
    Optionally the verifier might summarize the evidence as well, such
    as reporting on the volume of evidence, the number of cast
    ballots, spoiled ballots, the volume of logs, etc.
 2. It might discover that the evidence is not correct and reports
    such. That report should be as detailed as possible so as to
    permit the public and electoral authorities to investigate the
    verification failure as precisely and efficiently as possible.

## Manifest

This subsystem's artifacts are found in the following locations:
 - *documentation*: TBD
 - *specification*: TBD
 - *source code*: TBD

@todo kiniry Where are the docs, specs, and code for this subsystem?

The following issues track the design and development of this
subsystem:
 - *development plan*: #187
 - *system description*: #190
 - *threat model*: #193
 - *domain model*: #191

## Glossary

Our system glossary is based upon the 
[Free & Fair Election Glossary](https://github.com/FreeAndFair/ElectionGlossary), 
which is in turn based upon the NIST Election Glossary.

## Requirements

The BVS 2020 system is based upon ElectionGuard.  ElectionGuard
already has a reference verifier created by Galois implemented in
Rust. We must either augment that verifier to include the verification
of new properties mandated by the design of our own (daughter)
cryptographic protocol, or we must implement our own independent
verifier. Since we need not run the verifier on SSITH hardware, this
choice is not forced upon up by the current (as of September 2019)
unavailability of the Rust toolchain upstream on RISC-V.

### Mandatory

- *[EVIDENCE_COMPLETENESS]* The Verifier must consume and verify all
  evidence provided by the Evidence Server.
- *[LOG_VERIFICATION]* All system logs aggregated into the evidence
  must be verified by the Verifier.
- *[SEMI-FORMAL_SPEC]* The verification algorithm must have a
  semi-formal specification.
- *[FORMAL_CORRECTNESS_SPEC]* The verification algorithm must have a
  formal correctness specification.

### Optional

- *[FORMAL_SECURITY_SPEC]* The verification algorithm should have a
  formal specification of the security properties that it checks and
  the formal meaning of the implication of said properties being
  valid.
- *[VERIFIER_SOUNDNESS]* The verifier should state that the evidence is
  verified if and only if it has all of the properties entailed by
  the verification definition.
- *[VERIFIER_COMPLETENESS]* The verifier should be able to check every
  property entailed by the verification definition.
- *[VERIFIER_ASSURANCE]* The verifier implementation should have a
  rigorous assurance case that relates the implementation to the
  verification algorithm's formal and semi-formal specifications.

## Documentation

1. The ElectionGuard cryptographic protocol is specified in rigorous
   natural language in the 
   [ElectionGuard specification](https://github.com/microsoft/ElectionGuard-SDK-Specification).
2. The [ElectionGuard cryptographic protocol]
   (https://github.com/microsoft/ElectionGuard-SDK-Specification/tree/master/Formal/cryptol) 
   is formally specified using [Cryptol](https://cryptol.net/).
3. The BVS 2020 cryptographic protocol will be specified in rigorous
   natural language in Q4 2019.
3. The BVS 2020 cryptographic protocol will be formally specified 
   in Cryptol and perhaps other formats in Q4 2019 and into 2020.

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
