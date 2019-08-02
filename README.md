[![pipeline status](https://gitlab-ext.galois.com/ssith/voting-system/badges/master/pipeline.svg)](https://gitlab-ext.galois.com/ssith/voting-system/commits/master)

# The BESSPIN Voting System
## Galois and Free & Fair, May 2019

# Overview

Galois and Free & Fair are pleased to present the BESSPIN Voting System (BVS).

The purpose of the BVS is to demonstrate the secure CPUs developed under the DARPA MTO System Security Integrated Through Hardware (SSITH) program. This demonstration vehicle is the focus of a long-term, fully open process of adversarial cyber-security testing, starting at DEF CON 27 in August, 2019 and continuing over the following year to DEF CON 28 in 2020 and beyond.

This public repo provides prospective adversarial testers with complete information, tools, specifications, and source code that was used to develop the 2019 release of the BVS. The intent is to provide the most open possible approach to testing, enabling testers to obtain the full build environment for the BVS, to build it from original sources, assess its strengths and weaknessess, and plan and develop possible exploits to compromise the BVS.
However, not every tester will wish to start with this “Build First” approach. Others may wish to begin with the “Attacker Quickstart” information in order to learn and use the tools and reference exploits provided for testers. Yet others may wish to learn about BVS with a more managable “short list” of documentation and information about BVS, rather than explore the full repo as needed to build the BVS.

# For All Testers

All testers should begin by reading the `Overview of BESSPIN Voting System` document at the top level in this repo. This document provides essential information about the current BVS release,  the 2019 goals and limits on testing, including the threat model and win conditions.

# Attacker Quickstart

The top-level directory `Attacker-Quickstart` provides the next level of information after the  `Overview of BESSPIN Voting System` document document, specfically about the facilities that this repo provides for exploit development.

# Documentation on BVS

The top-level directory `BVS-Documents` provides the next level of information after the  `Overview of BESSPIN Voting System` document, about the BVS system’s design and functions.

# Support for System Build

The remainder of this repo provides the ability to build the BVS including source code (`source`); specifications (`specs`); hardware sketches and schematics (`hardware`); documentation of the build environment (`developer-documents`); the top-level `Makefile` and related files (`burn_to_flash.sh`, `startup.gdb`); and .git* files.

In addition, this repo contains one other source directory for a component that is not part of BVS per se, but is part of the test environment. The http-log-listener directory has the source code for a software component that runs on a separate dedicated server that shares the test environment’s LAN with the BVS Smart Ballot Box systems. The logging software’s purpose is to receive log data sent by each Smart Ballot Box. Such log consolidation is an important convenience for the operators of the test environment to be able to view the activity occuring on the Smart Ballot Box units as the testers interact with them.

This repository also contains submodules for dependencies that we manage in other git repositories:
- the RISC-V port of FreeRTOS, which is the lightweight real-time OS used for the BVS Smart Ballot Box;
- the top-level toolset for the BESSPIN project;
- the “government furnished equipment” (GFE) repository, which contains bitstreams to be uploaded on the FPGAs, and nix shell scripts for build set-up.

In order to update those submodules, remember to either clone the
repository using the `--recursive` switch or use the `git submodule
update --init --recursive` command to update submodules.

The system build process relies on several technologies:
- The core components of the BVS are implemented in the C programming language, using the `gcc` and `clang` (LLVM)
compilers. C is used because the BVS must run on both COTS hardware as well as SSITH
secure RISC-V CPUs, and because some SSITH performers are building
customized versions of the LLVM compiler.
- SSITH CPUs are all based upon the RISC-V Instruction Set Architecture
(ISA).  Thus, if we must provide any low-level code blobs for the BVS
in assembly or binary format, they will be written in RISC-V assembly
code.  Currently there is no such code, nor is it necessary at the moment.
- High level specification of BVS is specified using the *Lando*
specification language, developed under the remit of the BESSPIN
project at Galois.  Lando is a system specification language geared
toward describing the shape, structure, behavior, and security of
high-assurance systems spanning hardware, firmware, and software.
- More detailed and low-level specifications of BVS are written in several different formal languages such as *Cryptol* a DSL for specifying and reasoning about bit-level algorithms, particularly cryptographic algorithms and protocols; 


