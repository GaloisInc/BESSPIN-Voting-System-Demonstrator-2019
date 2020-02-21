# Static and Runtime Assurance based on Formal Verification of the BESSPIN Voting System

The assurance case for the BESSPIN Voting System spans multiple specification
languages and tools that we use to satisfy requirements and specify subsystem
components, data types, runtime verification and correctness properties.

# BVS 2019 Current Status

## Cryptol Specifications

Based on the requirements that every secure component in BVS must have
cryptographic integrity and that all cryptographic operations used by
submodules must have formal assurance available, our formal
specification is mainly in Cryptol, a domain specific language tailored
for cryptographic algorithms. We also use the SAW tool, which leverages
mathematical solvers to find counterexamples when program code does not
agree with its specification. The Cryptol work can be found in the
`cryptol` folder.

## Static Assurance

We have provided algebraic specifications, derived from specifications written
in Cryptol and Lando, for the crypto, logging, and controller (sbb) components.
These specifications are written in ACSL.

We then use these algebraic specifications to specify contracts (pre- and
postconditions, again in ACSL) for the C implementations of these components. We
use Frama-C/WP with runtime error annotation generation to check that each
function satisfies its contract and is type-safe.

The static assurance case is partially complete. Currently, the tool is not able to
verify that every function meets its specification. Often this is due to
completeness issues, but it is possible some contracts are not correct.

A summary of the Verification Conditions (VCs) generated and automatically discharged for each component is as follows:

|Component|VCs generated|VCs discharged|
|---------|------------:|-------------:|
|Crypto   |117          |97            |
|SBB      |905          |780           |
|Logging  |747          |747           |

These results were generated using:
* GIT Branch: master
* GIT Commit: c02dc4a76a94b7b5177ca9938a721c2b5c451342
* Toolset: Frama-C 19.0

## Dynamic Assurance

In addition to ACSL specifications, each submodule includes a suite of unit
tests (both positive and negative cases). These tests live in the [tests](source/tests) subdirectory.

# BVS 2019 Future Work

In the future we plan to finish the following specifications and
formally verify their implementations:
- `base64.acsl` (see `Base64.cry`)
- `secure_log.acsl` (see `Logging.cry`)
- extended contracts for the AES-specific C functions (see `AES.cry` and
  related Cryptol specs)
- global and typed invariants based on algebraic specification
- provide a full tabular and compositional summary of Frama-C analyses
- provide a full analysis of code coverage via runtime verification

# BVS 2020 Assurance Plan

@todo kiniry Write plan for full assurance case for BVS 2020.
