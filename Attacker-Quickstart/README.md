# Documents to help attackers get started on the system

This directory contains several simple exploits with step-by-step directions using the peek-poke server on the reference CPU, demonstrating several techniques you may find useful for writing your exploits. The exploits described here will work on the reference system, but are intended to fail on the target systems; they are meant as a starting point to get you up and running on your own exploits quickly.

# Background

The Voting Village will have access to the [smart ballot box (SBB) source code](../source) running on 3 hardware implementations. The reference system is a RISC-V processor with no security hardening; the two target systems are RISC-V processors with security extensions. Each system is run as a processor emulated on an FPGA. For a quick guide to RISC-V see [RISC-V in a Nutshell](./RISC_V_NUTSHELL.md). 

Each of the different hardware implementation is running the same software; this document shows how to implement some exploits in this software which will run on the reference system. Despite the fact that this same software is running on the target systems, the exploits described here will not work on the target systems. The target systems have security features that are intended to thwart exploits that would work on the insecure reference system; your goal is to create an exploit for the target systems using an attack which is in scope. For more context on the target systems and the acceptable win conditions, see the Overview document.

For the purpose of crystal-box testing, the SBB source code contains a peek-poke server which allows you to read (peek) and write (poke) the contents of a function called `malware()`. There are almost no restrictions on what `malware()` is permitted to do. It occupies the same memory space as the SBB code, and there are no software protections against writing over executable memory. This function is filled with NOP instructions to be overwritten with whatever you please, which will likely be binary corresponding to RISC-V 32-bit assembly instructions. You can interact with the peek-poke server by sending commands via `curl`. Check out [the peek-poke server README](./PEEKPOKE_README.md) for full usage instructions.

If you would like to use `malware()` to change instructions in other functions, you can use `objdump` to find the memory location of the section you’d like to change. You can then get the hex values of the assembly you’d like that section to contain, then send assembly that writes those hex values to the memory location of your choice to live in the `malware()` function. Once it’s filled, run `malware()` via the tool. If you would like to use tools like `objdump` you will need to use the RISC-V 32 bit version; Galois has provided a VM that has the RISC-V toolchain.

# Directory Contents

- [AES-key-to-display](./AES-key-to-display) is the simplest and most verbose example of how to use the peek-poke server. Start with this one. This exploit walks through how to write the ballot box LCD display value to be the location of the AES key.

- [all-barcodes-are-valid](./all-barcodes-are-valid) is an example of how to overwrite instructions in the SBB code. You can't write instructions directly to the SBB code, but you can write instructions to the `malware` function that will write to the SBB code. This exploit walks through how to overwrite the function responsible for validating barcodes to always return `BARCODE_VALID`.

- [accept-all-paper](./accept-all-paper) is an example of how to overwrite a function call in the SBB code with a different function call. The trick here is that functions are called using the `jal` instruction which is a relative jump, so you must compute the relative offset of the function you want to jump to. This exploit walks through how to change the control flow after a ballot has been inserted to immediately cast the ballot.

- [accept-my-ballot](./accept-my-ballot) is a more complicated example of how to redirect control flow in the SBB code to jump into the `malware` function, perform a computation, and then jump back into different places in the SBB code depending on the result of the computation. This example also discusses the expected format for valid barcodes. This exploit walks through how to check whether a ballot has a specific barcode (one that say, you crafted yourself), and if so, validate that ballot. 

# Debug tips

Common problems:

* If you're getting error messages or missing tools, make sure you're running in the nix-shell & using the RISC-V 32-bit version.
    * Try not to have a native/x86 compilers or compilation tools in your PATH at the same time so you don’t accidentally trigger any other gcc, clang, or binutils tools accidentally.
* Make sure you're compiling your exploits for 32-bit RISC-V, not 64-bit
* When writing to the malware function using the peek-poke server, make sure you are writing within the `nop` space, and not smashing the stack setup instructions at the beginning of the function.
* Mind the endianness (assembling switches the order of each byte).
* If `run_exploit.sh` is failing: 
    * Make sure you've set the IP of the server correctly.
    * Double-check that you have the correct `malware()` start address.
* If you are poking the server manually, remember to also request that the server `run` the `malware()` function.
