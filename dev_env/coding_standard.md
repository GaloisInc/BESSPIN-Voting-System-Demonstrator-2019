# BESSPIN Voting System - C Coding Standard

This document defines the C Coding Standard to be used on the BESSPIN Voting System (BVS) Project.

As far as is possible, this document refers to pre-defined standards that are freely available.

## Module languages and identification

The code shall be organized into modules, each of which has a ".h" and a corresponding ".c" file.

All code will comply with the "C99" version of the ISO C standard.

Additionally, all modules will identify if they are to be coded in Frama-C/ACSL. Note - it is possible for a module to have a .h file coded in Frama-C/ACSL, while its .c file is "normal" C99 file, such as a device driver which exports a Frama-C compatiable API to its clients.

Frama-C/ACSL modules will be coded in the common intersection of the language subsets supported by Frama-C plug-ins: VAL, WP and RTE.

## Coding Rules

As far as possible, code will comply with the Barr Group's Embedded C Coding Standard, unless any such rule contradicts the requirements of Frama-C usage. See [Barr Standard](https://barrgroup.com/Embedded-Systems/Books/Embedded-C-Coding-Standard) for more details.

## Style and Formatting

Code should be formatted with the `clang-format` tool with standard options defined by the project's `.clang-format` file.

As a starting point, the formatting style will be based on the standard LLVM style, but with the option "ReflowComments" set to "false" to avoid corruption of ACSL. See the clang-format [style options](https://clang.llvm.org/docs/ClangFormatStyleOptions.html) for more details.

## Compiler warnings

All code shall compile (through either GCC or LLVM) with no warning messages resulting with all standard warning messages enabled. Particular compiler options will be set and maintained in the project's Makefile.

## Size measurement

The size of code modules will be measured using the "Sloc" measure reported by the Frama-C "Metrics" plug-in.
