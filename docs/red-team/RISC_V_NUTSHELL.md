# RISC-V In a Nutshell
_(Or, what you need to know to do the usual hacks.)_

All of the CPUs in this project are running virtually
on FPGA hardware, but from the software's perspective, none of
that is visible. Instead, it's all RISC-V, plus various security
features that the different teams have added.

## Why not just x86 or ARM?

Because what would you do if you could do a CPU architecture over from
scratch? You could simplify things. You could remove legacy features that
nobody uses but which complicate everything else "just in case" they do get
used. You could pick and choose your favorite features from every other CPU
architecture. As such, RISC-V is showing great promise and has a lot of
support from industry. And, because FPGAs are fast enough and big enough, we
can run real software on a variety of different RISC-V "soft" implementations
without having to wait for "hard" silicon to get fabricated. Sure, the FPGA
versions are slower and burn more power than dedicated ASICs, but they work.

You may want to peruse the
[RISC-V instruction set architecture docs](https://content.riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf),
a [nice summary by Adam Langley](https://www.imperialviolet.org/2016/12/31/riscv.html),
or the [Wikipedia page](https://en.wikipedia.org/wiki/RISC-V).

This document presents a high level overview of
the ISA and some essential elements like how function calls
and returns work.

## RISC-V principles and basics

If you're familiar with other RISC instruction sets, what you'll find most
striking about RISC-V is how _unsurprising_ it is. There are 32
general-purpose integer/pointer registers and 32 more floating point
registers. Every instruction is 32-bits wide and is word aligned. There are
no branch delay slots (e.g., MIPS), register windows (e.g., SPARC), or
conditional execution (e.g., ARM). It's really easy to get up to speed on
RISC-V.
(Some extensions
will do variable-length instructions, and there's a "compressed ISA"
extension that does 16-bit wide instructions. For now, let's keep it simple
and stick with the standard 32-bit instructions.)

You'll notice there are four "base" architectures and a pile of
extensions. For now, let's just stick with the RV32I (32-bit instruction
set). Different RISC-V implementations will implement different extensions,
depending on the market where they're targeted. A common ("G") set of
extensions include integer multiplication and division ("M"), atomicity
instructions ("A"), and single/double-precision floating point ("F" and
"D"). Again, we're going to stick with the basics for now.

Each instruction, as with all classic RISC architectures, tends to do just one
thing. For example, while an x86 `CALL` instruction saves several things on the
stack, then branches, the RISC-V has no call instruction at all, and instead has a variety of "jump
linked" instructions. All they do is copy the program counter
to a specific register (for later returning) and jump to the target. They don't manipulate the stack pointer or
spill any registers to memory. You'll see a `call` pseudo-instruction in the assembly code,
but it's nothing more than a more accessible name for this linked
jump. You'll similarly see `ret` pseudo-instructions, but they're also just
jumps. All of the work to push state from the registers to the stack and
restore it later is handled in software.

## Calling conventions

If you're used to thinking "I'll just overwrite the return address on the
stack", it's not necessarily that simple. Instead, the standard calling
convention is that the return address is stored in register `x1` (also
called `ra` for "return address"). This means
a simple, no-op, *leaf function* will just jump to `ra` and call it a day.

Here's a really simple example:

```c
/* no-op function */
void foo(void) { }
```

Results of `riscv32-unknown-elf-gcc -S -O foo.c`:

```assembly
foo:
    ret
```

Results of `riscv32-unknown-elf-gcc -S foo.c` (no optimization):

```assembly
foo:
    addi    sp,sp,-16
    sw      s0,12(sp)
    addi    s0,sp,16
    nop
    lw      s0,12(sp)
    addi    sp,sp,16
    jr      ra
```

Several things are interesting here.
The unoptimized version is moving around the stack pointer to make room
for all the space that it doesn't need for local variables. You should
also note that `jr ra` (jump to the return address)
is the same as the `ret` pseudo-instruction. Sometimes the disassembler
gives you one and sometimes the other. Go figure.

If you disassemble a large program, you'll see these preamble and cleanup
sequences, as you see here in the unoptimized version, all over the place.
Of course, you can also see how an optimizer has the
opportunity to remove them when they're not doing useful work.

`sw` is a store-word instruction. In this case, it's writing a callee-save
register to the stack so it can use the register locally. 
Similarly, `lw` is a load-word instruction, which is restoring the
callee-save register prior to returning to the caller. Again, the
optimizer noticed that the code body never needed to use register `s0`
so there's no point in saving and restoring it, therefore it could
get rid of all the preamble and cleanup.

We know that register `x1` is also called `ra` because, by convention, it's used for a
return address. What about the rest of them? If you flip to page 121 in that
PDF with the instruction set (labeled "page 109"), you'll see all the
mnemonics for all the registers along with their common uses.

|Register|ABI Name|Description|Saver|
|--------|--------|-----------|-----|
| `x0`   | `zero` | Hard-wired zero | |
| `x1`   | `ra`   | Return address | Caller |
| `x2`   | `sp`   | Stack pointer | |
| `x3`   | `gp`   | Global pointer | |
| `x4`   | `tp`   | Thread pointer | |
| `x5`   | `t0`   | Temporary link register | Caller |
| `x6-7` | `t1-2` | Temporaries | Caller |
| `x8`   | `s0/fp` | Saved register/frame pointer | Callee |
| `x9`   | `s1`   | Saved register | Callee |
| `x10-11` | `a0-1` | Function arguments / return values | Caller |
| `x12-17` | `a2-7` | Function arguments | Caller |
| `x18-27` | `s2-11` | Saved registers | Callee |
| `x28-31` | `t3-6` | Temporaries | Caller |
| `f0-7` | `ft0-7` | FP temporaries | Caller |
| `f8-9` | `fs0-1` | FP saved registers | Callee |
| `f10-11` | `fa0-1` | FP arguments / return values | Caller |
| `f12-17` | `fa2-7` | FP arguments | Caller |
| `f18-27` | `fs2-11` | FP saved registers | Callee |
| `f28-31` | `ft8-11` | FP temporaries | Caller |

The important distinction here is between *callee-saved* and *caller-saved*
registers. This is the *calling convention* for RISC-V binaries.
[Here's a more detailed spec](https://riscv.org/wp-content/uploads/2015/01/riscv-calling.pdf).

If you're implementing a very tiny function, you're welcome to use the
caller-saved registers (`t0-6`) as temporaries and you have no obligation to
save their prior values. On the other hand, if you're implementing a bigger
function that needs more registers, you're welcome to use all the
callee-saved registers (`s0-11`), but you're responsible for writing their
original values out to memory and restoring them before you return.

Also, notice that arguments to most functions will be passed in registers
`a0-7` without touching the stack at all. This makes it a bit harder to
convert a buffer overflow into a functioning exploit, but it's not
impossible. Before that, though, let's put it all together with some
seemingly simple C code that has a few simple functions and constants:

```c
#include <stdio.h>

void print_int(int a) {
    printf("%d\n", a);
}

int sum(int a, int b) {
    return a + b;
}

void bar(int a, int b) {
    print_int(a);
    print_int(b);
    print_int(sum(a, b));
}
```

And, here's the result of running `riscv32-unknown-elf-gcc -S -O dumb.c` with annotations:

```assembly
print_int:
    addi  sp,sp,-16             ; move the stack pointer down 
    sw    ra,12(sp)             ; save our return address on the stack
    mv    a1,a0                 ; set the second argument for printf from our parameter
    lui   a0,%hi(.LC0)          ; load high bits of address for the format string
    addi  a0,a0,%lo(.LC0)       ; add in the low bits of address for the format string
    call  printf                ; branch to the printf function (also overwrites ra)
    lw    ra,12(sp)             ; restore the return address
    addi  sp,sp,16              ; restore the stack pointer
    jr    ra                    ; return
sum:
    add   a0,a0,a1              ; a0 (argument and return value) gets a0 + a1
    ret
bar:
    addi  sp,sp,-16             ; move the stack pointer down
    sw    ra,12(sp)             ; save our return address on the stack
    sw    s0,8(sp)              ; save one of the callee-save registers so we can use it
    sw    s1,4(sp)              ; save another of the callee-save registers so we can use it
    mv    s1,a0                 ; s1 gets the first argument from a0
    mv    s0,a1                 ; s0 gets the second argument from a1
    call  print_int             ; we're printing our first argument, already in a0
    mv    a0,s0                 ; setting up for the next call
    call  print_int
    add   a0,s1,s0              ; the optimizer inlined the call to sum!
    call  print_int
    lw    ra,12(sp)             ; restore the return address from the stack
    lw    s0,8(sp)              ; restore s0 (callee-save)
    lw    s1,4(sp)              ; restore s1 (callee-save)
    addi  sp,sp,16              ; restore the stack pointer
    jr    ra                    ; return
.LC0:
    .string    "%d\n"
```

You might ask, "why is the code for `bar` saving the values passed to it in
`a0` and `a1`?" Because it cannot count on `print_int` to preserve them.
By putting them in callee-save registers `s0-1`, `print_int` must guarantee that
those values will survive.

You might also note that the compiler inlined the call to `sum`. If it
hadn't, then you'd see the arguments placed in `a0` and `a1`, with the
result appearing in `a0` when complete.

## So how do I do ROP or return-to-libc on this thing?

There are some papers on this, including
[Buchanan et al., 2008](http://cseweb.ucsd.edu/~savage/papers/CCS08GoodInstructions.pdf).
They weren't doing RISC-V, but many of the same ideas should apply.

- Because instructions are all 32 bits wide and word aligned (at least, how
  we're doing it), there's no jumping into the middle of an instruction.

- You're still looking for gadgets: sequences of instructions ending in `jr
  ra` or `ret` (same thing) or other sorts of computed jumps.

- You probably are looking for a target function where you don't care about what
  happens after it's done; your goal is to set up the arguments to the
  function in the registers `a0-7`. It will be particularly straightforward
  to deal with single-argument functions, since `a0` is used both as the
  inbound parameter and outbound return value, so you'll find lots of
  gadgets that write to `a0` then return.

- In both `bar` and `print_int`, above, you can see that each ends with an
  instruction sequence to restore the stack. You should be able to use these,
  along with your initial buffer overflow, to build a ROP chain.

You might not need to do that at all, though. Our "peekpoke" web server
gives you a kilobyte of stack buffer that you can overflow, allowing you to
overwrite the last return address to have been saved on the stack,
somewhere up there, and with that you should just be able to branch directly to
machine code that you put into that stack buffer. Use your own machine code
to construct calls wherever you want.

## How are you protecting against these kinds of attacks?

Right now, we have a number of different RISC-V implementations that run on
our FPGA. Our vanilla `chisel_p1` implementation has no MMU, no memory
protections, no write-xor-execute, no stack canaries, nothing. Write and
execute anywhere!

This is great for testing attacks, but your goal, as the attacker, is to mount
the same sorts of attacks against one of our other RISC-V implementations.
Each one has its own security mechanisms.

_(Insert useful descriptions of other implementations here?)_

## Is this a realistic threat scenario?

For the ballot box computer, we're basically handing you a buffer overflow
opportunity on a silver plate, as well as giving you arbitrary read access
to any memory. (Or, at least, we're giving you these things on the vanilla
`chisel_p1`.) These represent two powerful attacks against the ballot box
computer.

_Is a buffer overflow vector reasonable?_ A "real" implementation of the
ballot box computer would have a variety of untrusted strings being thrown at it,
whether from its "real" networking paths or even from the QRcode on the
ballot. As such, this sort of threat is reasonable to appear, somewhere,
in a real implementation. We're just making it easier.

_Is arbitrary read access to memory reasonable?_ In the same way that
buffer overflows can lead to arbitrary code execution, they can also lead to
exfiltration of arbitrary secrets. Again, we're just making it easier.
