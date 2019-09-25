# BESSPIN Voting System (BVS) 2020 Smart Ballot Box (SBB)

The remit of a top-level subsystem `README.md` is as follows, as
specified in the Project Plan and [issue #152](https://gitlab-ext.galois.com/ssith/voting-system/issues/152).

```
Write the top-level `README.md` for the subsystem using the Free &
Fair template.  That template includes an executive summary (max 1
paragraph), an overview (max 1 page), a manifest (a table indicating
where to find more information), a glossary of terminology (or pointer
to a glossary), a high-level set of mandatory and optional
requirements, a manifest of documentation, a summary of the validation
and verification methodology and a manifest of those artifacts, and a
summary of contributors and funders.
```

## Executive Summary

A *Smart Ballot Box* (SBB) permits a voter to securely store a legal,
marked paper ballot.  The main function of the SBB is to determine
whether or not an inserted piece of paper is a legal ballot for the
current election, and to reject ballots that are not part of the
current election.
   
## Overview

## Manifest

This document summarizes the SBB.  The informal specifications of the
SBB are found in `specs/lando/sbb`.  Formal specifications of the SBB
are found in the ACSL files located in `source/include/sbb` and
related dependent subsystems (`logging` and `crypto`), the Cryptol
specifications found in `specs/cryptol`.

## Glossary

*Ballot Box*
: definition
*Illegal Ballot*
: definition
*Legal Ballot*
: definition
*Marked Paper Ballot*
: definition
*Paper Ballot*
: definition
*Smart Ballot Box (SBB)*
: permits a voter to securely store a legal, marked paper ballot.  The
main function of the SBB is to determine whether or not an inserted
piece of paper is a legal ballot for the current election, and to
reject ballots that are not part of the current election.

## Requirements

### Mandatory Requirements

### Sugggested Requirements

## Documentation

The documentation of the SBB is found mainly in the `specs/lando/sbb`
directory.  In particular, there you will find:

| File                     | Description |
| ------------------------ | ----------- |
| `development_plan.lando` | The summary of the *project plan* for the design, development, and assurance of the SBB subsystem. |
| `sbb.lando`              | The *domain model* for the SBB subsystem and its static architecture. |
| `sbb_hardware.lando`     | The *domain model*, *requirements*, *scenarios*, and *events* for the SBB's hardware. |
| `sbb_security.lando`     | The *requirements*, *scenarios*, and *security properties* of the security subsystem of the SBB. |
| `requirements.lando`     | The *requirements* for the SBB subsystem. |
| `scenarios.lando`        | The *scenarios* of the SBB subsystem. |
| `events.lando`           | The *events* of the SBB subsystem. |
| `specs/asms`             | The ASMs describing the SBB's dynamic architecture. |
| `specs/cryptol`          | The Cryptol specifications of many of the SBB's features and protocols. |
| `specs/feature_model.cfr` | A feature model describing the SBB's product line. |
| `specs/sbb-api.md` | A summary of the overall API of the SBB software. |
| `specs/sbb-asm.md` | A textual specification of the SBB's dynamic architecture via an ASM. |
| `specs/visio/BDD_architecture.*` | A graphical depiction of the SBB's static architecture. |

## V&V Methodology and Artifacts

- explain use of ASMs
- explain use of ACSL
- explain use of Cryptol and SAW
- explain use of host tests
- explain use of bottom implementation(s)
- explain use of smoketests
- explain use of simulation
- explain how FreeRTOS is used and relates to the implementation

## Contributors

This subsystem was:
 - designed by ...
 - implemented by ...
 - validated and verified by ...

This R&D was funded by the DARPA MTO SSITH program.  *Add appropriate
DARPA reference and disclaimer here.*

