# References for Performers Onboarding to the BESSPIN Voting System Project

This directory contains several papers and a book to bootstrap contributors
about our applied formal methods-based design, development, and assurance
process and methodology.

## An Introduction to Formal Methods

  1. We use applied formal methods to specify, test, and reason about the
     systems we create.  A (ten year old) background paper about formal methods
     in industry is _[Formal Methods: Practice and Experience]_ by our
     colleagues Woodcock, Larsen, Bicarregui, and Fitzgerald.
     
  2. A more recent taste about what applied formal methods looks like in the
     21st century is found in our paper
     _[Continuous Formal Verification of Amazon s2n]_ by Chudnov et al.

  3. We gave a background talk on modern applied formal methods entitled
     _[Formal Methods Need Not Be Black Magic]_ at the [RISC-V Summit] in 2018.

## Our Process and Methodology

  4. A short summary of our approachable verification-centric development
     process and methodology is found in our 2009 Formal Methods research paper
     _[Secret Ninja Formal Methods]_. This paper and development method were
     advocated for by a NIST report
     _[Dramatically Reducing Software Vulnerabilities (NISTIR 8151)]_
     submitted to the White House in 2016.

  5. For many years we used this methodology to create verifiable
     object-oriented systems in lvarious programming anguages, such as Java,
     Eiffel, and C#. Examples of such are found in our paper
     _[A Verification-Centric Software Development Process]_. A core part of
     our methodology is Design-by-Contract (DBC), a programming practice that
     focuses on writing formal specifications first, and writing program code
     that fulfills those specifications second.

  6. The approach used for BESSPIN Voting System project is summarized
     in a [Vimeo lecture series by Joe Kiniry].

## Specification Languages

  6. System specifications are written in a specification language named
     _Lando_ that we are creating as a part of the overarching BESSPIN project.
     Lando is the granddaughter of the [_BON_ specification language],
     which is summarized in the paper _[Business Object Notation (BON)]_, and
     the _[Clafer]_ specification language, summarized in the paper
     _[Clafer Tools for Product Line Engineering]_  by Antkiewicz et al.

  7. The BON language and method are described in detail in the book
     _[Seamless Object-Oriented Software Architecture]_ by Walden and Nerson.

  8. In order to keep formal specifications consistent with implementations and
     informal and semi-formal system specifications (such as requirements), we
     use and build tools based upon underlying theories of refinement.  Some of
     these foundations are summarized in our paper
     _[Ensuring Consistency between Designs, Documentation, Formal Specifications, and Implementations]_.

## Tools and Technologies

  9. For the projects we are running now we are obligated to use verifiable,
     secure C code as our implementation language.  Thus, we are using tools
     like _[Cryptol]_, _[SAW]_, _[Frama-C]_ and _[CBMC]_ to formally assure
     that our code conforms to its (Cryptol and _[ACSL]_) specifications. You
     will find Clafer, Lando, BON, and Cryptol specifications in [`/specs`]
     and you will find ACSL specifications throughought [`/source`].

[Cryptol]: https://cryptol.net/
[SAW]: https://saw.galois.com/
[Frama-C]: https://frama-c.com/
[CBMC]: http://www.cprover.org/cbmc/
[ACSL]: https://frama-c.com/acsl.html

[`/specs`]: ./../../specs
[`/source`]: ./../../source

[A Verification-Centric Software Development Process]: A_Verification-Centric_Software_Development_Process
[Formal Methods: Practice and Experience]: Formal_Methods_Practice_and_Experience.pdf
[Continuous Formal Verification of Amazon s2n]: Continuous_Formal_Verification_of_Amazon_s2n.pdf
[Formal Methods Need Not Be Black Magic]: Formal_Methods_Need_Not_Be_Black_Magic.pdf
[Secret Ninja Formal Methods]: Secret_Ninja_Formal_Methods.pdf
[Dramatically Reducing Software Vulnerabilities (NISTIR 8151)]: Dramatically_Reducing_Software_Vulnerabilities.pdf
[Business Object Notation (BON)]: Business_Object_Notation.pdf
[Clafer Tools for Product Line Engineering]: Clafer_Tools_for_Product_Line_Engineering.pdf
[Seamless Object-Oriented Software Architecture]: Seamless_Object-Oriented_Software_Architecture.pdf
[Ensuring Consistency between Designs, Documentation, Formal Specifications, and Implementations]: Ensuring_Consistency_Designs_Documentation_Specifications_Implementations

[RISC-V Summit]: https://tmt.knect365.com/risc-v-summit/
[Vimeo lecture series by Joe Kiniry]: https://vimeo.com/showcase/1498714
[_BON_ specification language]: http://www.bon-method.com/
[Clafer]: https://www.clafer.org
