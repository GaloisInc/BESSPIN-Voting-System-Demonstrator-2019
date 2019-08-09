

# Frequently Asked Questions about the BESSPIN Voting System, funded by the DARPA SSITH program in order to demonstrate and red team secure RISC-V CPUs

By Joe Kiniry, Dan Zimmerman, and others \
Galois ([https://galois.com/](http://galois.com/)) and Free & Fair ([https://freeandfair.us/](https://freeandfair.us/)) \
August 2019

**Q. What is SSITH?**

A: 

*   System Security Integration Through Hardware & Firmware
*   A DARPA funded program that aims to protect systems against classes of hardware vulnerabilities exploited through software.
*   There are several research organizations working on different approaches to securing hardware.
*   Galois is building the BESSPIN Voting System as a vehicle to demonstrate the secure hardware features.
*   Galois is also building out a tool set that will evaluate the effectiveness of the secure hardware features.

**Q. What SSITH CPUs are at DEF CON 2019?**

A: SSITH performers have been working very hard at having alpha versions of the first processors in the SSITH program ready for DEF CON.  These processors were meant to be finished by April of 2020, so anything we have at DEF CON is very early and somewhat lucky.  

We have three entities working hard on getting RISC-V microcontrollers ready for DEF CON, and as of 7 August 2019 we have one working RISC-V from the SRI/Cambridge team (called a CHERI RISC-V), but while it can be red teamed at DEF CON, it cannot yet run the Voting System demonstrator.

Unfortunately, despite their best efforts, the teams working on the other two SSITH secure processors could not get them working with the full voting demonstrator in time for DEF CON 2019.  In particular, getting all of the I/O for the demonstrator operational was a key challenge.  That being said, we have SSITH secure CPUs at DEF CON for red teaming in simulated environments that complement the hardware demonstrations on baseline RISC-V CPUs.

 \
We aim to have ten (10) SSITH CPUs ready for demonstration at DEF CON 2020: five microcontrollers running FreeRTOS and five “desktop” CPUs running Linux or FreeBSD.

** \
Q. What is the BESSPIN Voting System (BVS)?**

A: The BVS is demonstration software that provides some of the functions of a typical voting system. The purpose of the BVS is to demonstrate how ordinary software can run on and be protected by securitized hardware: the RISC-V processors being developed by 6 teams funded by the SSITH program. The BVS was developed to be available for adversarial cyber-security testing, including an ambitious test exercise of transparent securitized hardware. Public access to BVS hardware and software at DEF CON 2019 is the start of year-long phase of adversarial testing. RISC-V secure processors developed by six teams funded by the SSITH program are used as the processors under the BVS.

**Q. Why aren’t all of the BESSPIN Voting System demonstrators running SSITH secure CPUs at DEF CON 2019?**

A: The SSITH program is still in its early stages.  Many teams had a basic simulated CPU working in April of this year, but turning a software simulated CPU into a working hardware-simulated CPU on an FPGA—especially a platform with a lot of extra devices like our BVS—is a tall order.  Teams simply couldn’t get enough SSITH secure CPUs done in time for DEF CON 2019.  Therefore, we have baseline RISC-V CPUs that have no added security features running the Voting System demonstrator at DEF CON 2019 and these are open for red teaming.  Given that the application running on these systems has a fairly good assurance case, any flaws found in those systems will relate directly to the vulnerabilities that are the focus of the SSITH program, and consequently be extremely useful to teams developing and testing their secure CPUs.

**Q. How will the exploits written during DEF CON be used in and useful to this R&D?**

 \
A: Successful exploits provide valuable feedback to SSITH performers that are developing secure CPUs.  They help those hardware designers “get into the heads” of talented software and hardware hackers.  Exploits that succeed on the unprotected system, but fail on a system with a SSITH processor, are also valuable as they focus on our attention on where the hardware helps and the software hurts.  Submitted exploits add to a reference set of exploits developed by SSITH teams and help to explain by example the kinds of vulnerabilities that SSITH processors are immune to.  Finally, any exploit author is welcome to toot their own horn about their expertise in writing exploits, demonstrate their practical knowledge about the RISC-V ISA, and their contributing to R&D focused on created secure hardware for the world.

**Q: Why is DARPA building a voting system? / When are people going to start voting on this system? / Is this system going to be used in the 2020 election?**

A: DARPA is not building a voting system. The BESSPIN Voting System (BVS) is demonstration software, loosely based on current typical voting systems. It is not designed or intended to be a real-world voting system. DARPA is funding its development as a means to public testing and demonstration of the effectiveness of securitized hardware technology being developed by DARPA's SSITH program.

**Q: How does this DARPA-funded Voting System demonstrator for SSITH secure hardware differ from the Microsoft ElectionGuard SDK?**

A: ElectionGuard is an open-source, high-assurance cryptographic software development kit (SDK) that enables election systems vendors to create voting systems that are end-to-end verifiable and support risk-limiting audits.  ElectionGuard is a Microsoft product developed in partnership with Galois and Free & Fair, and will be released under the MIT open source license. 

The BESSPIN Voting System uses proof-of-concept, demonstration software. It is meant to test and demonstrate new ways of designing secure hardware, being developed as part of DARPA’s SSITH program and applicable to a wide range of systems such as vehicles, servers, etc. It is not meant to be a usable election system that can be deployed. 

**Q: What is SHIELD?**

A:  SHIELD (Supply Chain Hardware Integrity for Electronics Defense) is a separate DARPA funded program which aims to combat counterfeit integrated circuits (ICs) by developing microscopic-scale chips (called dielets) built with encryption, sensors, near-field power and communications that can be inserted into the packaging of ICs.  We aim to demonstrate a SHIELD at DEF CON in 2020.

**Q: Is the voting system demonstrated at DEF CON 2019 End-to-End Verifiable (E2E-V)?**

A: No, it is not.  The system demonstrated this year does have an open cryptographic protocol that provides evidence of vote secrecy, integrity, provenance, and other cryptographic properties, but it is not end-to-end verifiable (E2E-V).  An E2E-V system will be demonstrated next year on SSITH secure hardware.

**Q: Will you be demonstrating a hand-marked paper ballot system?**

A: Yes, we will demonstrate a hand-marked paper ballot system running on SSITH hardware at DEF CON 2020.  It will complement the BMD-based accessible voting system first demonstrated at DEF CON 2019.  We simply could not demonstrate a hand-marked paper ballot system—which we believe is incredibly important—at DEF CON 2019 because we simply did not have enough time to build it for this year.

**Q: Does the Ballot Marking Device demonstrated at DEF CON 2019 use the same Ballot Marking Device software that was demonstrated at the Aspen Security Forum by Microsoft?**

A: Yes, in the main it is the same open source software, VotingWorks’s BMD available on GitHub here: [https://github.com/votingworks/bmd](https://github.com/votingworks/bmd).  The only changes that we have made are to the system’s look/skin (effectively, a new stylesheet) and to its cryptographic backend (a few lines of Typescript), so that it can communicate with the BESSPIN Voting System’s Smart Ballot Box.  Our reuse of VotingWorks’s BMD source code demonstrates the ideas, power, and practicality of the open source movement.

**Q: Will this open source project accept contributions?**

A: This project is like any other open source project, insofar as we welcome interest from potential contributors.  Given the use of the system as a secure hardware demonstrator for the DARPA SSITH program, we have strong controls over who can merge into the development tree, how proposed changes are reviewed, etc.  Since the software is GPL-licensed and publicly available on GitHub, anyone is welcome to clone it, fork it, experiment with it, etc., as long as they adhere to the license.

**Q: Why does the Smart Ballot Box source code contain an AES key?  That’s a terrible idea!**

A: We know.  The AES key that is in the source code is there as a placeholder for a key that is loaded into the device, either via compilation (today) or a formally verified hardware security module (for DEF CON 2020).  The point of putting the key in plain sight at a known address is that we are mimicking what many systems that do not have hardware security modules (HSMs) do today: hold secret keys in DRAM while they perform encryption, decryption, and secret key-based hashing.  A SSITH secure CPU must be able to protect the integrity and secrecy of such memory regions—that’s one of the main focuses of the research program.  So even if the bad guy knows that there is a cryptographic key in the system, and exactly where the key resides, they should still have no means by which to read, leak, side-channel (through digital information flow or timing), or exfiltrate the key.

**Q: How does the system prove that the open source code is actually running on the hardware?**

A: This demonstration voting system uses a formally verified secure (measured) boot to prove that the (deterministically) compiled voting system software and all of its dependencies (drivers, the RTOS itself, and the state of the devices and their firmware) is exactly what is loaded onto the hardware and initialized.  This year’s demonstration does not use a hardware security module, but the system we intend to demonstrate at DEF CON 2020 will.  

The distrustful red team member would choose a random development laptop, do a clean install of a random distribution of Linux, install the necessary underlying tooling from random sources while checking code hashes and digital signatures, review the hardware, firmware, and source for the system, deterministically rebuild the system from scratch, regenerate that binary image’s hash, and compare that hash to the measure in the secure boot image.  Note that, since secure boot also measures the static and dynamic state of the system’s firmware, devices, DRAM image, and (eventually) CPU/SoC architectural state, one can also have assurance that devices and the SoC design were also not tampered with.

**Q: How do we know that this system does not have a backdoor?**

A: The system includes an informal and formal specification of its behavior.  We used several applied formal methods technologies to rigorously show (through runtime verification) and formally prove (through static formal verification) that the implementation behaves exactly as specified, no more, no less.  Using such a rigorous development scheme it is effectively impossible to insert a backdoor, since you can re-run the proofs yourself and re-compile the entire system’s hardware, firmware, and software from the ground up.  These are the same techniques we are using to formally verify cryptographic libraries for Amazon and others (see [https://galois.com/project/amazon-s2n/](https://galois.com/project/amazon-s2n/)).  Also, all of this complements our answer to the question, “How does the system prove that the open source code is actually running on the hardware?” above.

**Q: Why implement the system in C?  Why not use a safe language like Rust?**

A: The SSITH program only supports the development of new secure compilers (for those teams that need special compilers) that are C and LLVM-based.  Thus, we have to build the demonstrator system in (again, formally verified) C.  We would love to implement a version in Rust, especially given all of the work that we are doing in Rust at Galois, such as c2rust and support for formally verifying Rust code using SAW. See [https://galois.com/blog/2018/08/c2rust/](https://galois.com/blog/2018/08/c2rust/) and [https://timtaubert.de/blog/2017/01/equivalence-proofs-with-saw/](https://timtaubert.de/blog/2017/01/equivalence-proofs-with-saw/) 

**Q: How does an election get tabulated with this BVS demonstration system?**

A: The paper ballots produced by the BMDs are the ballots of record in our pretend elections.  These paper ballots are hand-tabulated at intervals throughout the day by human beings, exactly as one would do in a small jurisdiction in the USA that hand-tabulates election results.  

The digital record of the election, which contains a cryptographic encoding of (purported) voter choices made by the voter via the air-gapped BMD, is also analyzed by the logging server and its contents are summarized live during the demo.  That cryptographic record would/should be used in the real world to audit an election, provide a cryptographic evidence-based foundation for forensic analysis, etc.

**Q: What license is the BESSPIN Voting System released under?**

A: The BESSPIN Voting System at the moment is the Smart Ballot Box, running on FreeRTOS, running on the SSITH Government Furnished Equipment (GFE), which contains one of several RISC-V CPUs.  Given the complexity of this systems stack, the answer to this question comes in several parts.



*   The BESSPIN Voting System Smart Ballot Box is released under the GPLv3 license.
*   FreeRTOS is released under the MIT open source license.
*   Our augmentations to FreeRTOS are consequently released under the MIT license.
*   The Government Furnished Equipment (GFE) is licensed under several licenses, as different subsystems therein are based upon different sources, both commercial and open source.
*   The RISC-V CPUs that ship on the GFE are licensed under two different licenses:
    *   Two of the Bluespec SystemVerilog-based cores (Piccolo RV32 and Flute RV64) supported by the GFE were developed by Bluespec and are released under the Apache License 2.0.
    *   The Bluespec SystemVerilog-based superscalar CPU (Tuba/Toooba superscalar RV64) supported by the GFE was developed by MIT (as RISCY-OOO) and augmented by Bluespec (as Tuba/Toooba) and is released under a combination of the MIT and Apache License 2.0 licenses.
    *   All of the Chisel-based cores (the Rocket-based RV32, the Rocket-based RV64, and the BOOM-based RV64) are released under the BSD license.

**Q: What is a red team participant permitted to do to attack this secure hardware demonstrator?**

A: It depends upon which demonstrator you are focusing on.  In general, red team participants are welcome to:

(a) interact with the demonstrator over two communication channels: 

    (1) the simulated serial interface (UART) via the supplied USB cable, and 	

    (2) the supplied Ethernet cable, and

    (b) load malware into the demonstrator over the provided HTTP interface supplied via the aforementioned Ethernet cable. \

Some of the demonstrators available at DEF CON 2019 may have a narrower red team framing than summarized above—it depends upon what hardware we have working on any given day. \

Red team participants are **not welcome to**:

*   interact with the provided USB cable as a general USB device,
*   attempt to induce hardware-based vulnerabilities in either the USB or Ethernet cable (e.g., please do not experiment with power glitching attacks—you could fry our expensive FPGA and the device is not built to be resistant to these kinds of attacks, as they are not the focus of this research program or demonstrator), or
*   physically manipulate the Smart Ballot Box hardware (no playing with wiring, pulling off buttons or displays, etc.).

### **Further, more technical questions**

**Q: Why is this voting system’s hardware better than hardware for normal voting systems?**

A: SSITH secure CPUs are being designed specifically to avoid the design flaws of currently available hardware—flaws that are exploited by malicious software to create a wide range of security vulnerabilities. The SSITH program’s hardware development includes a focus on several specific classes of vulnerability, with a goal of building new systems for which these vulnerabilities simply do not exist. _These benefits will apply not only to future voting systems, but to any future security-critical systems that today are built on inherently vulnerable PC-era hardware, such as those seen in other critical infrastructure industries like the power grid, food supply, nuclear power plants, etc._

**Q: Why is this new technology needed for voting systems? Is it better than the current efforts in improving election security?**

A: Current election security efforts focus on paper ballots as a method to detect vote counting errors that might be related to hardware or software problems, including cyber-attacks. It’s not enough to be able to detect errors created by today’s easily hackable voting systems; we need to have voting machines that are immune to a broad range of cyber-attack methods. Voting machines in particular have a requirement that that they can only be used in the certified “factory-fresh” condition, with no modifications. But today’s hardware and software is simply unable to meet this requirement. Neither election officials nor voters have any assurance that a voting machine has not been tampered with. But the next generation of securitized hardware will be able to meet this requirement.

**Q: Who is Free & Fair?**

A: Free & Fair is a company devoted to doing public good research and development in trustworthy elections.  For the past several years, Free & Fair has been Galois “doing business as” Free & Fair.  By the end of 2019 Free & Fair will be an Oregon public benefit (Class B) corporation.  Free & Fair/Galois has been responsible for several elections projects, including:

*   the _Future of Voting_ project for the U.S. Vote Foundation, which describes the foundation of, and mandatory requirements, cryptography, and technology for, public elections using the internet,
*   the Colorado Risk-Limiting Audit system, which is used in Colorado and elsewhere across the U.S.A. to audit elections,
*   advising federal agencies and conducting investigations relating to elections technology and security, and
*   Microsoft’s ElectionGuard product, a software developer’s kit for end-to-end verifiable voting and risk-limiting audits.

**Q: Does the system use paper ballots?**

A: Yes, the system does use paper ballots.  Moreover, we at Galois and Free & Fair we believe that paper ballots are mandatory for all elections, and paper ballots are the ballots of record in all elections.  Extra digital information about the voting process—such as cryptographically secret cast vote records—can help audit an election, but cannot and should not be used to tabulate an election.

**Q: Does the system include a Ballot Marking Device?**

A: Yes, the system demonstrated uses an open source Ballot Marking Device developed by [VotingWorks](https://voting.works/) with technical and financial assistance from Galois, Free & Fair, and Microsoft.

**Q: Why use a Ballot Marking Device at all?**

A: We believe that voters with disabilities must be able to vote independently.  The only way to accomplish that today is via an accessible Ballot Marking Device (BMD).  The VotingWorks BMD that we are demonstrating is such a BMD.  By federal statute, all polling places must have an accessible BMD.

**Q: Does the system use barcodes?**  

A: Yes, the DEF CON 2019 system uses a 2D barcode.  We recognize that the use of barcodes in voting systems is a very controversial topic. The reason why we chose to use one in the 2019 system is that we needed an inexpensive and quick means by which to encode a small cryptographic piece of information in a machine-readable fashion. The only technology solution we could see that was reasonable on our development timeline was to use an open barcode format containing an openly described data format. The human-readable vote on the paper ballot is the ballot of record. We intend that the hand-marked paper ballot system we demonstrate at DEF CON 2020 will not use barcodes.

**Q: What information is stored in the barcode?**

A: The information in the barcode is not tabulated to determine an election outcome—it is only used to (a) ensure that only legal ballots are inserted into the Smart Ballot Box and (b) audit the election and red team contest.  It consists of several pieces of information that are encrypted using AES and digitally signed using an AES-CBC MAC, including the voter’s choices and the ballot expiration time.  The key used for the MAC and the expiration time indicate whether the paper ballot is a legal ballot.  The voter’s choices are used as a CVR for election auditing.

**Q: Are blockchains a part of this solution?**

A: No, this system contains no blockchain-based technology.  Moreover, we at Galois and Free & Fair believe that there is no place for blockchains in technology for public elections.  See the short article [“Blockchains and Elections”](https://freeandfair.us/articles/blockchains-and-elections/) at Free & Fair for our position, and the article [“Are Blockchains the Answer for Secure Elections? Probably Not”](https://www.scientificamerican.com/article/are-blockchains-the-answer-for-secure-elections-probably-not/) at Scientific American for a longer read article with input from several of our scientific colleagues.  [https://freeandfair.us/articles/blockchains-and-elections/](https://freeandfair.us/articles/blockchains-and-elections/)  [https://www.scientificamerican.com/article/are-blockchains-the-answer-for-secure-elections-probably-not/](https://www.scientificamerican.com/article/are-blockchains-the-answer-for-secure-elections-probably-not/) 

**Q: Does this system support Internet/remote voting?**

A: There is no Internet/remote voting involved in this R&D.  If you want to learn about that topic, we recommend the report "The Future of Voting: End-to-End Verifiable Internet Voting - Specification and Feasibility Study", which we co-wrote and edited for the U.S. Vote Foundation.  [https://www.usvotefoundation.org/E2E-VIV](https://www.usvotefoundation.org/E2E-VIV)

_This research was developed with funding from the Defense Advanced Research Projects Agency (DARPA). The views, opinions and/or findings expressed are those of the author and should not be interpreted as representing the official views or policies of the Department of Defense or the U.S. Government._

_Distribution Statement "A" (Approved for Public Release, Distribution Unlimited)_