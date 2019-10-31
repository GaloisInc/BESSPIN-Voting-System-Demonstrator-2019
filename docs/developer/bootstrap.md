# Bootstrapping and Understanding of Free & Fair R&D for BESSPIN

## An Introduction to Formal Methods

1. We use applied formal methods to specify, test, and reason about
   the systems we create.  A (ten year old) background paper about
   formal methods in industry is 
   "[Formal Methods: Practice and Experience](/BVS-Documents/onboarding/WoodcockEtAl09.pdf)" 
   by our colleagues Woodcock, Larsen, Bicarregui, and Fitzgerald.

2. A more recent taste about what applied formal methods looks like in
   the 21st century is found in our paper 
   "[Continuous Formal Verification of Amazon s2n](/BVS-Documents/onboarding/ChudnovEtAl18.pdf)" 
   by Chudnov et al.

3. We gave a background talk on modern applied formal methods entitled
   "[Formal Methods need not be Black Magic](/BVS-Documents/onboarding/Formal_Methods_Need_Not_Be_Black_Magic__2018_RISC-V_Summit_.pdf)" 
   at the RISC-V Summit in 2018.
   
## Our Process and Methodology

4. A short summary of our approachable verification-centric
   development process and methodology is found in our Formal Method
   2009 research paper 
  "[Secret Ninja Formal Methods](/BVS-Documents/onboarding/Secret_Ninja_Formal_Methods.pdf)."
   This paper and development method were advocated for by a NIST
   report (NISTIR 8151) 
   "[Dramatically Reducing Software Vulnerabilities](/BVS-Documents/onboarding/BlackEtAl16.pdf)" 
   which was submitted to the White House in 2016.

5. For many years we used this methodology to create verifiable
   object-oriented system in languages like Java, Eiffel, and C#.
   Examples of such are found in our paper 
   "[A Verification-Centric Software Development Process](A_Verification-Centric_Software_Development_Process.pdf)." 
   A core part of our methodology is Design-by-Contract (DBC), a
   programming practice that focuses on writing formal specifications
   first, and writing program code that fulfills those specifications
   second.
   
## Specification Languages

6. System specifications are written in a specification language
   called Lando that we are creating as a part of the overarching
   BESSPIN project.  Lando is the granddaughter of the BON
   specification language, which is summarized in the paper 
   "[Business Object Notation (BON)](/BVS-Documents/onboarding/Business_Object_Notation.pdf)," 
   and the Clafer specification language, summarized in the paper 
   "[Clafer Tools for Product Line Engineering](/BVS-Documents/onboarding/AntkiewiczEtAl13.pdf)"
   by Antkiewicz et al.

## Tools and Technologies

7. For the projects we are running now we are obligated to use
   verifiable, secure C code as our implementation language.  Thus, we
   are using tools like 
   [Cryptol](https://cryptol.net/), 
   [SAW](https://saw.galois.com/), 
   [Frama-C](https://frama-c.com/), and 
   [CBMC](http://www.cprover.org/cbmc/) to formally
   assure that our code conforms to its (Cryptol and 
   [ACSL](https://frama-c.com/acsl.html))
   specifications.  You will find Clafer, Lando, BON, and Cryptol
   specifications in the [specs directory](/specs) of the BESSPIN Voting System
   project.  You will find ACSL specifications throughout the 
   [source directory](/source) of the project.
   
## Demonstrators and Products

8. The top-level web page that characterizes the work we did for DARPA
   for DEF CON 2019, which includes the BESSPIN Voting System 2019 as
   well as its dependencies (our version of FreeRTOS, and the
   underlying Government Furnished Equipment that includes the RISC-V
   softcore processors and more), is located here:
   https://securehardware.org

9. Our live development BESSPIN Voting System project is currently
   hosted in our semi-public GitLab instance, hosted at Galois.  We
   intend to make that project public before the end of the year and
   do development in public.  We use several tools for distributed
   collaborative development such as Keybase, Google Meet, etc.
   GitHub is used to snapshot development releases to the public.

10. Our product development on Microsoft ElectionGuard is published
    via Microsoft's GitHub organization.  The 
    [ElectionGuard SDK GitHub project](https://github.com/microsoft/ElectionGuard-SDK) 
    is the top-level for this product.  It references several
    other projects that contain the specification, a reference
    verifier, and more.  Our 
    [fork of the SDK implementation sub-project](https://github.com/GaloisInc/ElectionGuard-SDK-C-Implementation) 
    in where the final development work is being done for the moment.
