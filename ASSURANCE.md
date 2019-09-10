# Static and Runtime Assurance based on Formal Verification of the BESSPIN Voting System

The assurance case for the BESSPIN Voting System spans multiple
specification languages and tools that we use to satisfy requirements
and specify subsystem components, data types, runtime verification and
correctness properties.

# Current Status

Based on the requirements that every secure component in BVS must have
cryptographic integrity and that all cryptographic operations used by
submodules must have formal assurance available, our formal
specification is mainly in Cryptol, a domain specific language tailored
for cryptographic algorithms. We also use the SAW tool, which leverages
mathematical solvers to find counterexamples when program code does not
agree with its specification. The Cryptol work can be found in the
`cryptol` folder.

For static assurance we use Frama-C, a modular static analysis framework
for the C language, to assure that our implementations conform to a
contract design written in ACSL and to provide an algebraic
specification either by extracting Cryptol specifications to C or by
formally describing some mission critical parts of the system in a
top-to-bottom style. This work is partially complete.

In this first phase of development [BVS
2019](https://gitlab-ext.galois.com/ssith/voting-system/-/milestones/19),
we have covered all methods with preconditions and postconditions
seamlessly refactoring code to be much more compliant with the Frama-C
EVA plugin. We put effort into algebraic specification, trying to
describe the crypto submodule in order to find equivalence relations
induced by the cryptographic properties. This is still an work in
progress.

In parallel to this formal verification activity, unit tests have been
derived from the specifications by using a slicing technique providing
both types: regular and malicious tests for all submodules. The reason
for the additional testing effort is that unit testing is
well-established in the software quality dynamic assurance process of
safety critical systems. Various tests can be seen in the `logging`,
`sbb` and `protocols` submodules.

# Future Work

In the future we plan to finish the following specifications and
formally verify their implementations:
- `base64.acsl` (see `Base64.cry`)
- `secure_log.acsl` (see `Logging.cry`)
- extended contracts for the AES-specific C functions (see `AES.cry` and
  related Cryptol specs)
- global and typed invariants based on algebraic specification

