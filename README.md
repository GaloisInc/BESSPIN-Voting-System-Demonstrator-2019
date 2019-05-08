% The BESSPIN Voting System
% Galois and Free & Fair
% May 2019

# Overview

Galois and Free & Fair are pleased to present the BESSPIN Voting
System (BVS for short).

The goal of the BVS is to demonstrate secure CPUs developed under the
DARPA MTO System Security Integrated Through Hardware (SSITH)
program.  This demonstration vehicle is the focus of a long-term, open
red team exercise, kicked off at DEF CON 27 in August, 2019.

# Project Organization

This repository contains documentation (`docs`), presentations
(`slides`), source code (`source`), and specifications (`specs`).
This top-level `README.md` summarizes the project and walks the reader
through the aforementioned artifacts in order to understand, port, and
modify the BVS.

# Technologies

Insofar as the BVS must run on both COTS hardware as well as SSITH
secure RISC-V CPUs, and because some SSITH performers are building
customized versions of the LLVM compiler, the core components of the
BVS must be implemented in the C programming language.  Thus, the core
programming technology used is C and the `gcc` and `clang` (LLVM)
compilers.

SSITH CPUs are all based upon the RISC-V Instruction Set Architecture
(ISA).  Thus, if we must provide any low-level code blobs for the BVS
in assembly or binary format, they will be written in RISC-V assembly
code.  Currently there is no such code.

We specify the BVS at the highest level using the *Lando*
specification language, developed under the remit of the BESSPIN
project at Galois.  Lando is a system specification language geared
toward describing the shape, structure, behavior, and security of
high-assurance systems spanning hardware, firmware, and software.

More detailed and low-level specifications of BVS are written in
several different formal languages:

- [Coq]
- [Cryptol]



