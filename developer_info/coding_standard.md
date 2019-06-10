# BESSPIN Voting System - C Coding Standard

This document defines the C Coding Standard to be used on the BESSPIN Voting System (BVS) Project.

As far as is possible, this document refers to pre-defined standards that are freely available.

## Module languages and identification

The code shall be organized into modules, each of which has a `.h` and a corresponding `.c` file.

Additionally, each modules will identify if it is to be coded in Frama-C/ACSL. Note: it is possible for a module to have a .h file coded in Frama-C/ACSL, while its .c file is a "normal" C99 file, such as a device driver that exports a Frama-C compatible API to its clients.

### C Source Code Verification Tool

All code will at least comply with the "C99" version of the ISO C standard.

Frama-C/ACSL modules will be coded in the common intersection of the language subsets supported by Frama-C plug-ins VAL, WP and RTE.

C modules will be coded in the intersection of the aforementioned Frama-C language subset (if said code is to be verified with any Frama-C plug-in) and the C language subset supported by our pinned version of SAW.

## Mixing Frama-C and C99 code

A Frama-C module can only #include a header file if that header file is also Frama-C, complying with the language subset implied above and containing appropriate ACSL contracts.

Example: Predefined FreeRTOS modules, such as ff.h, as _not_ Frama-C compatible (and probably never will be) and therefore cannot be included and called directly from Frama-C code. To call such units, a "thick binding" module must be created that provides a Frama-C friendly API onto the underlying module.

## Coding Rules

As far as possible, code will comply with:
 - the [Barr Embedded C Coding Standard](https://barrgroup.com/Embedded-Systems/Books/Embedded-C-Coding-Standard), unless any such rule contradicts the requirements of verification tool usage, and
 - the [SEI CERT C Coding Standard](https://resources.sei.cmu.edu/downloads/secure-coding/assets/sei-cert-c-coding-standard-2016-v01.pdf), unless any such rule contradicts the requirements of verification tool usage.

As far as reasonable, source code comments will comply with:
 - usage conventions for ACSL, as documented by the Frama-C documentation, and
 - the [KindSoftware Coding Standards](http://kindsoftware.com/documents/whitepapers/code_standards/), as exemplified by the SHAVE case study.

## Primitive Types

The known-width primitive types in C99, defined in `<stdint.h>`, should be used in preference to the implementation-defined types of earlier standards. For example, use `int32_t` rather than `int`.

## CheriABI compatibility

This section will expand to cover coding rules that are required for compatibility with the Cambridge team's CheriABI and modified LLVM.

1. Do not cast pointers.
2. If you absolutely must cast a pointer to an integer type, then you must cast to `intptr_r`, defined in C99's `<stdint.h>`.

## Style and Formatting

Code should be formatted with the `clang-format` tool with standard options defined by the project's `.clang-format` file.

As a starting point, the formatting style will be based on the standard LLVM style, but with the option "ReflowComments" set to "false" to avoid corruption of ACSL. See the clang-format [style options](https://clang.llvm.org/docs/ClangFormatStyleOptions.html) for more details.

## Compiler warnings

With all standard warning messages enabled, all code shall compile (through either GCC or LLVM) with no warning messages. Particular compiler options will be set and maintained in the project's Makefile.

## Code measurements

The size and complexity of code modules will be measured using the `Sloc` measure reported by the Frama-C "Metrics" plug-in.  Code size can also be measured with the `sloccount` and `cloc` tools, both of which are available via Homebrew or otherwise.

The following guidelines should be attended to with regard to code size and complexity:
 - functions should have fewer than 20 NCSS (Non-Commenting Source Statements), and
 - functions should have a McCabe cyclomatic complexity of no greater than 5.
