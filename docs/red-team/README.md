This “Attacker QuickStart Guide” provides specific information for
those planning on participating in adversarial cyber-security testing
of the BESSPIN Voting System (BVS).

# Background

The BVS is a demonstration voting system being funded by DARPA’s SSITH
(System Security Integrated Through Hardware and Firmware)
program. SSITH’s goal is to develop new technologies that will enable
chip designers to safeguard hardware against all known classes of
software-exploitable vulnerabilities, such as memory errors,
information leakage, and code injection.

As a set of voting system demonstration software running on SSITH
hardware, the BVS demonstration system enables adversarial
cyber-security testing in which attackers attempt to show the
limitations of SSITH-based secure hardware, in the context of voting
system.

This “Attacker QuickStart Guide” is for those who are planning on
participating in an in-person testing event, either the first one at
DEF CON 2019, or subsequent events leading up to DEF
CON 2020. Prospective attackers should first read the “Overview of the
BESSPIN Voting System” document to learn about the BVS, the threat
model for testing, attacker rules of engagement, and in-scope and
out-of-scope attacks.

# How To Use This Guide

This Guide provides specifics about how attackers can choose to attack
the BVS. We’ve developed exploit methods and reference exploits that
can save you time and effort in understanding how to attack the BVS.

We’ll start with an overview of testing environment itself, and the
facilities for you to interact with both the reference system (the BVS
on ordinary hardware) and the target systems (the BVS on multiple
types of SSITH securitized hardware). Then we’ll focus on the
facilities provided for attacking them, and the reference exploits
that you can use to both to successfully attack the reference system,
and to see how the exploits don’t work on target systems. They are
meant as a starting point to get you up and running on creating your
own exploits quickly.

The intent of this Guide and these tools is to quickly get some
attackers past the “analyze the target system” phase of work and
directly jump in to attacking the BVS. Other attackers may prefer to
do extensive analysis via rebuilding the system and observing it; in
addition to this Guide, the rest of this BVS repo provides such
attackers with all the information needed to analyze the BVS in
detail.

# The Test Environment

The BVS 2019 version is a pair of devices: a ballot marking device
(BMD) and a Smart Ballot Box (SBB), described in more detail in the
“Overview of the BESSPIN Voting System” document at the top level of
this repo, which you must read first in order to be able to follow
this Guide.

The target for attack is the SBB only, and no other part of the test
environment. In BVS 2019, only the SBB is built using SSITH
securitized hardware.

The DEF CON 2019 Voting Village test environment contains a number of
pairs of BMD and SBB, including: one pair that is the “reference
system” in which the SBB runs on ordinary hardware including a RISC-V
processor with no security protections; and at least two pairs of
“target system” in which the SBB runs on RISC-V processors with SSITH
security protections. Each system is run as a processor emulated on an
FPGA. For a quick guide to RISC-V see [RISC-V in a
Nutshell](RISC_V_NUTSHELL.md)

Each of the different hardware implementations is running the same
software. This Guide shows how to implement some exploits in this
software that will run on the reference system. While these exploits
do not work on the target systems, your goal is to create an exploit
for the target systems using an attack that (a) is in-scope for the
attacks, and (b) meets the win conditions, both as described in the
Overview document.

In addition to the BMDs and SBBs, the test environment also includes
components that are not part of the BVS, but are included to
facilitate testing. Each SBB is equipped with two interfaces that
would not be part of an SBB in a real voting system: a simulated
serial interface (UART) via a supplied USB cable, and (2) an Ethernet
cable.

Attackers are welcome to interact with an SBB via either, but this
Guide focuses on attacks that are launched via network access to a
part of the SBB that is also provided for the convenience of attackers
— a web service called “peek-poke” that — described in the next
section — makes it easy for attackers to load malware into an SBB’s
memory, and to execute the malware, without first having to discover a
software vulnerability and develop an exploit for it.

In addition, the SBBs’ network interface is used to connect the SBBs
to a shared Log Server, which consolidates the event logs of all the
SBBs, in order to provide real time access to logs — rather than
having to shut down an SBB and copy log data from local
storage. Again, though this logging function is not part of the BVS
per se, the Log Server enables the test environment’s monitoring staff
to have quick access to data that might support an attacker’s claim to
a successful attack.

A couple of diagrams, provided in this Attacker-QuickStart part of the
repo, illustrate the test environment.

Attackers are expected to behave within the rules of engagement in the
Overview document, and refrain from denial-of-service attacks and
physical attacks. Attackers are not welcome to: interact with the USB
cable as a general USB device; physically manipulate the SBB hardware
(tampering with wiring, removing buttons or displays, etc.); attempt
to induce hardware faults via the USB and Ethernet interfaces,
e.g. power glitching attacks that in addition to being out of scope,
could also destroy the demonstration systems’ FPGA and prevent any
further testing.

# The Attackers’ Toolset

The BVS test exercise is intended to be completely open, a crystal-box
rather than black-box process. As a result, this repo contains all the
information needed to build an SBB, starting with the
[smart ballot box (SBB) source code](../source) for the SBB software
that runs on the reference system and the target systems.

The centerpiece of the attackers toolset is a network service called
peek-poke that was added the SBB to make it very convenient to
demonstrate sample exploits, and to enable testers to come up with
their own exploits. Included along with the Guide are sample exploits
described in a cookbook manner, walking through several simple
exploits using the peek-poke server on the reference CPU,
demonstrating several techniques you may find useful for writing your
exploits.

The peek-poke server provides an HTTP service that attackers can use
via a browser, or via a shell and curl to send commands. This
Attack-QuickStart part of the repo includes a man page with specific
usage for the web service’s interfaces: hello, peek, and poke. Using
the peek interface, attackers can request read the SBB’s memory at
specified start address and length; if the memory region is readable,
“peek” returns the contents of the memory region. Using the poke
interface, attackers can access the contents of a function called
`malware()`. Aside from the 1-kilobyte size of the memory region
containing `malware()`, there are almost no restrictions on what
`malware()` is permitted to do. It occupies the same memory space as
the SBB code, and `malware()` is free to attempt to write over
executable memory — which not controlled in the unprotected reference
system. The `malware()` function is filled with NOP instructions to be
overwritten with whatever you please, which will likely be binary
corresponding to RISC-V 32-bit assembly instructions. You can interact
with the peek-poke server by sending commands via `curl`. Check out
[the peek-poke server README](PEEKPOKE_README.md) for full usage
instructions.

If you would like to use `malware()` to change instructions in other
functions, you can use `objdump` to find the memory location of the
section you’d like to change. You can then get the hex values of the
assembly you’d like that section to contain, then send (via poke)
assembly instructions that write those hex values to the memory
location of your choice to live in the `malware()` function. Once it’s
filled, you can run `malware()` via the peek-poke interface. If you
would like to use tools like `objdump` you will need to use the RISC-V
32 bit version; Galois has provided a VM that has the RISC-V toolchain
— also part of this repo.

# The Reference Exploits

In addition to this Guide (and other materials like supporting
diagrams, the peek-poke man page, and the short intro to RISC-V) you
will also find a set of reference exploits. Each one is sub-directory
under the `Sample-Exploits` directory, containing a README that
provides the cookbook-like instructions, and a C source code file, and
a corresponding file of assembly language instructions. Each cookbook
provides background on how the exploit was constructed, as well as
specific usage with the peek-poke server to insert and run the
assembly language fragment in `malware()`.

As an added convenience, you will also find a script `run_exploit.sh`
that can be used to automate much of the interaction with peek-poke
via curl. Each reference exploit’s README provides directions on how
to use `run_exploit.sh`.

The reference exploits are:

- [AES-key-to-display](Sample-Exploits/AES-key-to-display) is the
  simplest and most verbose example of how to use the peek-poke
  server. Start with this one. This exploit walks through how to write
  the ballot box LCD display value to be the location of the AES key.

- [all-barcodes-are-valid](Sample-Exploits/all-barcodes-are-valid) is
  an example of how to overwrite instructions in the SBB code. You
  can't write instructions directly to the SBB code, but you can write
  instructions to the `malware()` function that will write to the SBB
  code. This exploit walks through how to overwrite the function
  responsible for validating barcodes to always return
  `BARCODE_VALID`.

- [accept-all-paper](Sample-Exploits/accept-all-paper) is an example
  of how to overwrite a function call in the SBB code with a different
  function call. The trick here is that functions are called using the
  `jal` instruction which is a relative jump, so you must compute the
  relative offset of the function you want to jump to. This exploit
  walks through how to change the control flow after a ballot has been
  inserted to immediately cast the ballot.

- [accept-my-ballot](Sample-Exploits/accept-my-ballot) is a more
  complicated example of how to redirect control flow in the SBB code
  to jump into the `malware()` function, perform a computation, and
  then jump back into different places in the SBB code depending on
  the result of the computation. This example also discusses the
  expected format for valid barcodes. This exploit walks through how
  to check whether a ballot has a specific barcode (one that say, you
  crafted yourself), and if so, validate that ballot.

As you develop your own exploits, here are a few debug tips. First,
make sure that you're compiling for 32-bit RISC-V, not 64-bit. Second,
mind the endianness (assembling switches the order of each
byte). Third, use the peek-poke server’s “hello” interface to get the
`entry_address` for the malware function, but be careful to not smash
the function setup instructions; with plenty of NOP space, you can
just decide to write a little bit after the setup. Also, if you are
poking the server manually (rather than using `run_exploit.sh`),
remember to also request that the server `run` the `malware()`
function. Finally, if `run_exploit.sh` is failing: make sure you've
set the IP of the server correctly; double-check that you have the
correct `malware()` start address.

# Process, Workflow, Submitting Exploits, and Getting Credit

Last but certainly not least, we encourage you to use this repo to
contribute exploits, seek feedback, and get credit — whether you are
in person at DEFCON or subsequent events, or preparing exploits for
later testing. Using the reference exploits as a model, you can
develop your own exploits, and document them with the same structure
as the sample exploits under the `Contributed-Exploits` directory: a
directory containing a README, C source, and assembly that’s used as
described in the README to run the exploit via the peek-poke
interface, or the `run_exploit.sh` script.

Following this process, you can use this repo to: submit your exploit
via a Merge Request that includes your directory that contains the
documentation and source of your exploit; get feedback and support via
creating new Issues and tracking responses to them.
