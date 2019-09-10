# BVS 2020 Assurance

See the top-level file `ASSURANCE.md` for a summary of our overall
assurance case.

## Artifacts Summary

The following artifacts focus on the implementation and assurance of
each subsystem:
 - a well-typed architecture of the domain model, including its
   external-facing API
 - a bottom implementation of the subsystem
 - a behavioral specification of the subsystem, using either or both
   ACSL or Cryptol
 - a set of generated unit tests, created by Frama-C and/or Cryptol or
   other tools
 - a set of hand-written subsystem and integration tests, which
   concretize the aforementioned requirements and scenarios into
   runtime verification artifacts
 - a set of hand-written formal specifications, which complement and
   extend the dynamic tests

Runtime verification (aka dynamic tests) and static analysis and
formal verification are used for developer-triggered and automated
continuous verification in our CI server.  We intend to primarily use
Frama-C and SAW for such assurance, perhaps complemented in edge cases
by other tools with which we have deep familiarity (e.g., SPIN,
UPPAAL, FDR4, and CBMC).

## Protocol Specification and Verification

For the traditional voting system, we will specify and reason about
that system’s BVS Protocol using Cryptol and SAW.  We do not intend to
mechanically reason about the security properties of the protocol
itself (using tools like EasyCrypt, CryptoVerif, or ProVerif).

For the E2E-V variant, we intend to extend the ElectionGuard SDK and
protocol and reuse much of its implementation and assurance case.  The
main extensions that must be made to the protocol and its
implementation include: incorporation of SHIELD technology in at least
one paper artifact (see below for more information on our planning for
such) incorporation of application and system log evidence from all
BVS subsystems into the overall cryptographic evidence of the election
