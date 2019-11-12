macOS as a Development Platform for the BESSPIN Voting System

Operating System Foundation
---------------------------

1. We support macOS 10.14 (Mojave) and 10.15 (Catalina) as
   development platforms.

Software Foundations
--------------------

2. Install Xcode from the App Store. After installing Xcode and launching it
once to install required additional components, install its commmand line
tools.
```
   xcode-select --install
```

3. Install Homebrew (https://brew.sh/), then install a few
   missing packages.
```
   brew install pkg-config gtksourceview gtksourceview3 libgnomecanvas libxml2 autoconf
```

    Set `PKG_CONFIG_PATH` to point to the right location:
```
    setenv PKG_CONFIG_PATH `echo /usr/local/opt/*/lib/pkgconfig | sed -e 's/ /:/g'`
```
    or
    export PKG_CONFIG_PATH=`echo /usr/local/opt/*/lib/pkgconfig | sed -e 's/ /:/g'`
```
   `pkg-config` does not know, by default, where to find all these
   `opt`-based packages; this environment variable fixes this. Use
   the appropriate command based upon your shell.

OPAM
----

4. Install and initialize `opam`, as some of the system's dependencies
   are installed via `opam`.

```
   brew install opam
   opam init  (respond 'y' and 'y' to two questions)
```

Frama-C
-------

5. Install Frama-C using `opam`
```
  opam install frama-c --unlock-base
```
   OPAM's OCaml is newer than Frama-C needs/uses.  The use of the
   `--unlock-base` switch permits OPAM to install an older,
   appropriate version of OCaml.

6. Check what version of Frama-C is installed and working.

  We have used Frama-C version 18.0 (Argon) and 19.0 (Potassium) for
  the development of BVS 2019.

  `frama-c --version`

LLVM (including clang)
----------------------

7. Install llvm/clang using Homebrew. Unlike Apple's LLVM distribution,
   it includes the `llvm-link` tool needed for SAW.

   7.1.  Install Homebrew LLVM via Homebrew: `brew install llvm`

   7.2.  To override Apple's version of LLVM globally, add
         `/usr/local/opt/llvm/bin` to the front of your shell's `PATH`
         by modifying your shell startup.
         This will cause Hombrew's LLVM and tools to be found before
         Apple's installation, which is in `/usr/local/bin`. If you
         do not want to override Apple's version of LLVM globally,
         you can manually add `/usr/local/opt/llvm/bin` to your path
         only in shells you are using to build this project.

Clang-Format
------------

Install Clang-Format.

8. `brew install clang-format`

SHAVE Smoketest
---------------

This set of tools should be enough to reproduce the Frama-C analyses
of the SSITH seedling SHAVE application software (if you have access
to that repository).

Coq
---

Even if you are not using Coq for formal proofs, it is required to build
the *BESSPIN Book*.

9. `opam install coq`
   `opam install coqide`

Installing Coq will sometimes recompile Frama-C.

Cryptol
-------

Install the latest release of Cryptol and its default SMT solver, Z3 from 
Microsoft, using Homebrew.

10. `brew install cryptol`
 
The resulting installation has Cryptol 2.8.0 and Z3 version 4.8.6.

If you need an older version of Cryptol, see the [Cryptol releases
page at GitHub](https://github.com/GaloisInc/cryptol/releases/).

Z3
--

If the aforementioned Homebrew install of Cryptol properly installed
Z3 as a dependency, no further action is necessary.  If you have
any problem, install release version 4.7.1 or 4.8.6 of Z3. 
Do not use any other releases; sometimes new releases break 
functionality upon which Cryptol depends. 

In order to install specific releases of Z3, directly download them
from `https://github.com/Z3Prover/z3/releases`, extract the Zip
archive, and move the extracted directory to somewhere in your `PATH`.

Yices
-----

Another solver that Cryptol can use is the Yices SMT solver from SRI.
Release 2.6.1 is required, and is available on Homebrew.

11. `brew install SRI-CSL/sri-csl/yices2`

SAW
---

Much of the work on the BVS and its dependencies used SAW version 0.3
and development versions before SAW 0.4 was released.

Obtain the current SAW release from the [SAW release webpage at
GitHub](https://github.com/GaloisInc/saw-script/releases).
On macOS Catalina, which is stricter about app notarization and
quarantine than Mojave, you must "un-quarantine" the SAW binary by
running:

 `xattr -d com.apple.quarantine /path/to/saw-0.4-OSX-64/bin/saw`

Git Submodules
--------------

Make sure to update all submodules of this project.  At this time, the
only submodule is our version of FreeRTOS.

12. `git submodule update --init`


GFE and BESSPIN Tooling
-----------------------

The Government Furnished Equipment (GFE) on which the Voting System
runs to demonstrate SSITH secure CPUs is a Xilinx FPGA platform (a
VCU118 with a variety of attached peripherals).  The supported 
development environment for the GFE, as well as for the custom EDA
tooling we have built for DARPA, is Linux.  As such, at this time we
do not suggest trying to use any of that tooling on macOS directly.
We currently have experimental Docker support for running on macOS
(and other Docker-capable platforms), but we make no guarantees 
about its functionality.

