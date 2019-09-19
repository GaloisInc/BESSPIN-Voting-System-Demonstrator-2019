# The BVS 2020 Protocols

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

The human principals in the BVS 2020 protocol are as follows:

1. An Election Commission made up of one or more Election Commissioners.
2. A Polling Place Supervisor who is responsible for a Polling Place by
   virtue of being responsible for the Polling Place Controller.
3. A Polling Place Worker who is in the role of a Voter Authenticator and thus
   is responsible for a Registration System.
4. A Polling Place Worker who is responsible for helping voters who have
   trouble of any kind in the Polling Place.
5. Any other members of the Public.
