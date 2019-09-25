[![pipeline status](https://gitlab-ext.galois.com/ssith/voting-system/badges/master/pipeline.svg)](https://gitlab-ext.galois.com/ssith/voting-system/commits/master)

# The BESSPIN Voting System

## Galois and Free & Fair, May-September 2019

# Overview

Galois and Free & Fair are pleased to present the BESSPIN Voting
System (BVS).

The BESSPIN Voting System (BVS) is a demonstration system being funded
by DARPA’s SSITH (System Security Integrated Through Hardware and
Firmware) program. SSITH’s goal is to develop new technologies that
will enable chip designers to safeguard hardware against all known
classes of software-exploitable vulnerabilities, such as memory
errors, information leakage, and code injection.

The BVS demonstration system is intended to showcase the SSITH
program’s results by showing how the innovations of “securitized
hardware” could be applied to a type of critical computing system that
is personally familiar both in use and in importance to millions of
Americans: voting systems. BVS is a combination of voting-system
demonstration software together with prototypes of securitized
hardware being developed by SSITH researchers.

This public repository provides prospective adversarial testers with
complete information, tools, specifications, and source code that was
used to develop the 2019 release of the BVS. The intent is to provide
the most open possible approach to testing, enabling testers to obtain
the full build environment for the BVS, to build it from original
sources, assess its strengths and weaknessess, and plan and develop
possible exploits to compromise the BVS.  

However, not every tester will wish to start with this “Build First”
approach. Others may wish to begin with the “Attacker Quickstart”
information in order to learn and use the tools and reference exploits
provided for testers. Still others may wish to learn about the BVS
with a more manageable “short list” of documentation and information,
rather than exploring the full repository.

# For All Testers

All testers should begin by reading the [Overview of BESSPIN Voting
System](Overview-of-BESSPIN-Voting-System.pdf) document at the top
level of this repository. This document provides essential information
about the current BVS release, the 2019 goals, and limits on testing
including the threat model and win conditions.

# Attacker Quickstart

The top-level directory [Attacker-Quickstart](Attacker-Quickstart)
provides the next level of information after the [Overview of BESSPIN
Voting System](Overview-of-BESSPIN-Voting-System.pdf) document
document, specifically about the facilities provided for exploit
development.

# Documentation on BVS

The top-level directory [BVS-Documents](BVS-Documents) provides the
next level of information after the [Overview of BESSPIN Voting
System](Overview-of-BESSPIN-Voting-System.pdf) document, about the BVS
system’s design and functions.

System design documentation is found in the [docs directory](docs).
In particular, that directory contains:
 - the [BVS 2020 System Specification](docs/BVS 2020 system specification.md)
 - the [BVS 2020 Protocol Specification](docs/protocol.md)
 - the [Smart Ballot Box Specification](docs/sbb.md)
  
# Support for System Build

The remainder of this repository provides the ability to build the BVS
including source code [source](source); specifications [specs](specs);
hardware sketches and schematics [hardware](hardware); documentation
of the build environment [developer-documents](developer-documents);
the top-level [`Makefile`](Makefile) and related files
(`burn_to_flash.sh`, `startup.gdb`); and `.git*` files.

In addition, there is one other source directory for a component that
is not part of the BVS per se, but is part of the test
environment. The [http-log-listener](http-log-listener) directory has
the source code for a software component that runs on a separate
dedicated server that shares the test environment’s LAN with the BVS
Smart Ballot Box systems. The logging software’s purpose is to receive
log data sent by each Smart Ballot Box. Such log consolidation is an
important convenience for the operators of the test environment to be
able to view the activity occuring on the Smart Ballot Box units as
the testers interact with them.

This repository also contains submodules for dependencies that we
manage in other git repositories:
- the RISC-V port of FreeRTOS, which is the lightweight real-time OS
  used for the BVS Smart Ballot Box;
- the top-level toolset for the BESSPIN project;
- the “government furnished equipment” (GFE) repository, which
  contains bitstreams to be uploaded on the FPGAs, and nix shell
  scripts for build set-up.

In order to update those submodules, remember to either clone the
repository using the `--recursive` switch or use the `git submodule
update --init --recursive` command to update the submodules.

The system build process relies on several technologies:
- The core components of the BVS are implemented in the C programming
  language, using the `gcc` and `clang` (LLVM) compilers. C is used
  because the BVS must run on both COTS hardware and SSITH secure
  RISC-V CPUs, and because some SSITH performers are building
  customized versions of the LLVM compiler.
- SSITH CPUs are all based upon the RISC-V Instruction Set
  Architecture (ISA).  Thus, if we must provide any low-level code
  blobs for the BVS in assembly or binary format, they will be written
  in RISC-V assembly code.  Currently there is no such code, nor is it
  necessary at the moment.
- High level specification of BVS is specified using the *Lando*
  specification language, developed under the remit of the BESSPIN
  project at Galois.  Lando is a system specification language geared
  toward describing the shape, structure, behavior, and security of
  high-assurance systems spanning hardware, firmware, and software.
- More detailed and low-level specifications of the BVS are written in
  multiple formal languages. These include *Cryptol*, a DSL for
  specifying and reasoning about bit-level algorithms, particularly
  cryptographic algorithms and protocols, and *ACSL*, the ANSI/ISO C
  Specification Language, for specifying and reasoning about the
  behavior of C programs.

# How to Contribute: Testing the BVS

We welcome all testers to not only perform testing, but also
contribute exploits to this repo. For those attending DEF CON 2019 or
subsequent testing events, the contents of this repo provide ample
resources for detailed preparation, or minimal preparation via the
Attacker Quickstart guide. 

## Live Red Teaming

The following lists the specific steps for how testers’ exploits can
be contributed in a live red teaming framing.

1. Finish reading this README, and the overview document [Overview of
   BESSPIN Voting System](Overview-of-BESSPIN-Voting-System.pdf). Make
   careful note of the threat model and win conditions of the
   system. Only exploits that are in-scope and also meet the win
   conditions with be recognized publicly as as “win” on the system.

2. Choose a target machine.  At DEF CON we have three systems
   available for hacking: 
- A baseline RISC-V microcontroller that has no security
      enhancements. This system can be used to test our your exploits
      on insecure hardware to ensure that they work as expected.
- An open hardware, open source CHERI-RISC-V processor developed
      by SRI and the University of Cambridge.
- A blackbox proprietary secure RISC-V processor.

3. Experiment with an existing exploit in the [Attacker-Quickstart
   directory](Attacker-Quickstart), or write an entirely new
   exploit.  In order to test the exploit, you can either run it in
   software simulation using Verilator, or you can load it onto the
   target machine you have chosen.  We suggest first simulating or
   loading it into a baseline RISC-V processor.

4. Ensure that your exploit provides third-party
   reviewable/demonstrable evidence that the exploit was
   successful. For some exploits, this might be realized via a
   physical mechanism (i.e., you will demonstrate it to organizers
   interactively at DEF CON), and for others, there may be digital
   evidence (i.e., a tampered system log).

5. When you are ready to contribute your exploit, create a personal
   fork of this repository, so that you can provide a merge/pull
   request when you wish to share it with the world and demonstrate
   its capability. We suggest that your exploit be shared in the
   Attacker-Quickstart directory, with a subdirectory with contents
   that follow the conventions of the reference attacks.

6. File an issue in this repo announcing your work to the test
   organizers. In that issue, point to your fork.

7. In the issue body and using the `red-team` labels, please summarize
   your exploit, including indicating which legal weakness you
   exploited (e.g., labels `buffer/memory error` or `information
   leakage`), the behavior of the exploit on insecure hardware, its
   behavior on one of the secure hardware systems, and what evidence
   it provides of your success. Indicate which CPU you targeted with
   the appropriate label, e.g. `baseline`, `SRI/Cambridge`,
   `proprietary`.

8. Talk to an organizer to indicate that you have filed an issue so
   that we can discuss your work face-to-face if desired. Organizers
   will immediately triage your issue and/or merge request.

9. Organizers will review the exploit and will keep you and the public
   up to date about their findings via a public discussion on the
   issue, by using workflow labels `under review`, `success`, `fail`,
   etc.  "Success" in the context of a label means that the exploit
   works on that CPU; "fail" means that it does not. Additional labels
   are used by organizers to label exploits or other code for future
   analysis.

10. Pay attention to the live screens in the testing venue, to see if
    your exploit succeeds or fails.

11. If your exploit is successful (a `CPU-hack` label is applied),
    organizers will summarize your work and success in public
    information on the projection screens at DEF CON or on social
    media.

## Asynchronous Red Teaming

@todo kiniry To be written.

# Credits

This DARPA-funded R&D represents the hard work of the following
employees of Galois and Free & Fair:
 - Alexander Bakst
 - Annie Cherkaev
 - Dan Wallach
 - Dan Zimmmerman
 - Daniel Wagner 
 - Dragan Stosic
 - Dylan Hand
 - Eric Wolridge
 - Flemming Andersen
 - Georgios Dimou
 - Haneef Mubarak
 - Jason Graalum
 - Joe Kiniry
 - Joey Dodds
 - John Sebes
 - Kenny Foner
 - Luke Myers
 - Max Waugaman
 - Michael Podhradsky
 - Nes Cohen
 - Niki Carroll
 - Noah Rich
 - Parker Southwick
 - Reuben Broadfoot
 - Rod Chapman
 - Shpatar Morina
 - Steven Osborn
 - Stuart Pernsteiner

The BMD we are using for DEF CON 2019 is based upon the open source
BMD developed by our friends at [Voting
Works](https://voting.works/). Thanks especially to Ben Adida.

Our fork of Voting Works's BMD for our DEF CON 2019 demonstration is
found on GitHub: https://github.com/GaloisInc/BESSPIN-BMD-2019

# Glossary

For a glossary of voting system terminology, see Free & Fair's
[Election Glossary project at
GitHub](https://github.com/FreeAndFair/ElectionGlossary).  That
glossary is, at the moment, a transliteration of the NIST VVSG
glossary with terms added according to our project needs.  

We also have an informal domain model specified in BON, found in
the [Specifications project at
GitHub](https://github.com/FreeAndFair/Specifications). That domain
model will be updated during BVS 2020 development.

