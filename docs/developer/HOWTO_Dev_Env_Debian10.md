Starting Point
--------------

1. Completely basic intall of Debian Buster RC1  in a VM under Parallels Desktop Pro 14 on a MacBook pro running MacOS 10.14.5

2. Created a single, standard user account "rchapman". This will be used from now on
for all steps below.

3. Installed Parallels Tools for Linux.

Basics
------

   su to "root"
   apt-get install emacs
   apt-get install gitk
   apt-get install git-gui
   add user "rchapman" to group "sudo" in /etc/group
   Reboot

OPAM
----

4. sudo apt update
   sudo apt upgrade
   sudo apt install opam
   sudo apt install mccs

5. opam init --solver=mccs (respond 'y' and 'y' to two questions)

6. Shutdown and restart Linux here to allow environment changes to take effect.

Frama-C
-------

See https://frama-c.com/install-18.0-Argon.html

6. opam install depext
   opam depext frama-c
   opam install frama-c

CLANG
-----

8. sudo apt install clang
   sudo apt install clang-format

      installs in /usr/bin/clang
      --versionb reports 7.0.1-8
      Main files in /usr/lib/llvm-7 including bin/llvm-link


MILESTONE 1
-----------

This set of tools should be enough to reproduce the Frama-C analyses
of the SHAVE application software.


COQ
---

Even if not usign Coq for formal proofs, it is needed to build the BESSPIN Book.

9. opam install coq
   opam install coqide



Z3 4.7.1
--------

Z3 (precisely version 4.7.1) is a pre-requisite for Cryptol.

Download the package for x64-debian-8.10 from https://github.com/Z3Prover/z3/releases
Extract the ZIP file and move the extracted directory to $HOME/tools

Edit $HOME/.profile to add $HOME/tools/z3*/bin to your PATH


Yices 2.6.1
-----------

Another pre-requisute for Cryptol

NOTE: do NOT try to use "apt-get" to install from SRI's repository - it doesn't
seem to work with Debian Buster.

Download the binary .tar.gz from yices.csl.sri.com
Unpack and move the resulting directory to $HOME/tools

Add $HOME/tools/yices-2.6.1/bin to your PATH


Cryptol 2.7.0
-------------

NOTE: do NOT install the standard Debian cryptol package using apt-get - this appears to be out of date.  Instead:

First, a legacy library is needed, so

  sudo apt install libtinfo5

Grab the tarball of Cryptol 2.7.0 for Ubuntu14.04 from https://github.com/GaloisInc/cryptol/releases/tag/2.7.0
Decompress the untar the tarball, and move the resulting directory to $HOME/tools

Edit $HOME/.profile to add $HOME/tools/cryptol*/bin to your PATH


SAW
---

The current version to use is
  saw-0.3-Ubuntu14.04-64.tar.gz
from https://github.com/GaloisInc/saw-script/releases

Download, decompress and untar that file.
Move the resulting directory to $HOME/tools

Add $HOME/tools/saw-0.3-Ubuntu14.04-64/bin to your PATH


NIX
---

sudo sysctl kernel.unprivileged_userns_clone=1
curl https://nixos.org/nix/install | sh
. $HOME/.nix-profile/etc/profile.d/nix.sh



GFE and BESSPIN Tooling
-----------------------

Building the GFE toolset needs to happen on a native Linux filesystem (not one shared with MacOS, for example), then we need to clone the GFE repo locally first.

cd $HOME
mkdir BESSPIN
cd BESSPIN
git clone git@gitlab-ext.galois.com:ssith/gfe.git
cd gfe
./init_submodules.sh

# Switch to the "develop" branch of the GFE repo
git checkout develop
git submodule update --init tool-suite
cd tool-suite
git checkout develop
sudo sysctl kernel.unprivileged_userns_clone=1
nix-shell

# Warning - this takes about 3 hours to build and install the first time you run it...
# and that's on a quad-core MacBook Pro...


Test RISCV Tools and GCC
------------------------

Log out and back in again to let the changes above take effect.

"cd" to voting-system/FreeRTOS-mirror/FreeRTOS/Demo/RISC-V_Galois_P1

then do

nix-shell
make all


This should use riscv32-unknown-elf-gcc to build and link "main_blinky.elf"
successfully.

CROSS-CHECK - content of $HOME/.profile
---------------------------------------

The final section of my $HOME/.profile now looks like this:

# opam configuration
test -r /home/rchapman/.opam/opam-init/init.sh && . /home/rchapman/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true

PATH=$HOME/tools/yices-2.6.1/bin:$PATH
PATH=$HOME/tools/z3-4.7.1-x64-debian-8.10/bin:$PATH
PATH=$HOME/tools/cryptol-2.7.0-Ubuntu14.04-64/bin:$PATH
PATH=$HOME/tools/saw-0.3-Ubuntu14.04-64/bin:$PATH
export PATH

if [ -e /home/rchapman/.nix-profile/etc/profile.d/nix.sh ]; then . /home/rchapman/.nix-profile/etc/profile.d/nix.sh; fi # added by Nix installer


Yours should look similar.


Z3 4.7.1
--------

Z3 (precisely version 4.7.1) is a pre-requisite for Cryptol.

Download the package for x64-debian-8.10 from https://github.com/Z3Prover/z3/releases
Extract the ZIP file and move the extracted directory to $HOME/tools

Edit $HOME/.profile to add $HOME/tools/z3*/bin to your PATH


Yices 2.6.1
-----------

Another pre-requisute for Cryptol

NOTE: do NOT try to use "apt-get" to install from SRI's repository - it doesn't
seem to work with Debian Buster.

Download the binary .tar.gz from yices.csl.sri.com
Unpack and move the resulting directory to $HOME/tools

Add $HOME/tools/yices-2.6.1/bin to your PATH


Cryptol 2.7.0
-------------

NOTE: do NOT install the standard Debian cryptol package using apt-get - this appears to be out of date.  Instead:

First, a legacy library is needed, so

  sudo apt install libtinfo5

Grab the tarball of Cryptol 2.7.0 for Ubuntu14.04 from https://github.com/GaloisInc/cryptol/releases/tag/2.7.0
Decompress the untar the tarball, and move the resulting directory to $HOME/tools

Edit $HOME/.profile to add $HOME/tools/cryptol*/bin to your PATH


SAW
---

We use a nightly build of SAW. The current version to use is
  saw-0.3-2019-05-27-Ubuntu14.04-64.tar.gz
from https://saw.galois.com/builds/nightly/

Download, decompress and untar that file.
Move the resulting directory to $HOME/tools

Add $HOME/tools/saw*/bin to your PATH


TO DO
=====

This not covered by this HOWTO (yet...)

1. Extra provers for Frama-C: cvc4

2. cBON and other lando/BON tooling.

3. Document preparation tools - latex, pandoc etc.
