# References for performers on-boarding to the BESSPIN Voting System project

This directory contains several papers and a book to bootstrap
contributors about our applied formal methods-based design,
development, and assurance process and methodology.

* An Introduction to Formal Methods

  1. We use applied formal methods to specify, test, and reason about
     the systems we create.  A (ten year old) background paper about
     formal methods in industry is 
     “[Formal Methods: Practice and Experience](WoodcockEtAl09.pdf)” 
     by our colleagues Woodcock, Larsen, Bicarregui,and Fitzgerald.
     
  2. A more recent taste about what applied formal methods looks like
     in the 21st century is found in our paper 
     “[Continuous Formal Verification of Amazon s2n](ChudnovEtAl18.pdf)” 
     by Chudnov et al.

  3. We gave a background talk on modern applied formal methods
     entitled 
     “Formal Methods need not be Black Magic” 
     at the [RISC-V Summit](https://tmt.knect365.com/risc-v-summit/) in 2018.

* Our Process and Methodology

  4. A short summary of our approachable verification-centric
     development process and methodology is found in our Formal Method
     2009 research paper 
     “[Secret Ninja Formal Methods](Secret_Ninja_Formal_Methods.pdf).”
     This paper and development method were advocated for by a NIST
     report (NISTIR 8151) 
     “[Dramatically Reducing Software Vulnerabilities](BlackEtAl16.pdf)” 
     submitted to the White House in 2016.

  5. For many years we used this methodology to create verifiable
     object-oriented system in languages like Java, Eiffel, and C#.
     Examples of such are found in our paper 
     “[A Verification-Centric Software Development Process](A_Verification-Centric_Software_Development_Process.pdf).”
     A core part of our methodology is Design-by-Contract (DBC), a
     programming practice that focuses on writing formal
     specifications first, and writing program code that fulfills
     those specifications second.

  6. The approach used for BESSPIN Voting System project is summarized
     in a 
     [Vimeo lecture series by Joe Kiniry](https://vimeo.com/showcase/1498714).

* Specification Languages

  6. System specifications are written in a specification language
     called *Lando* that we are creating as a part of the overarching
     BESSPIN project.  Lando is the granddaughter of the 
     *[BON specification language](http://www.bon-method.com/)*, 
     which is summarized in the paper
     “[Business Object Notation (BON)](Business_Object_Notation.pdf),” 
     and the Clafer specification language, summarized in the paper 
     “[Clafer Tools for Product Line Engineering](AntkiewiczEtAl13.pdf)” 
     by Antkiewicz et al.

  7. The BON language and method are described in detail in the book
     "[Seamless Object-Oriented Software Architecture](Seamless_Object-Oriented_Software_Architecture.pdf)" 
     by Walden and Nerson.

  8. In order to keep formal specifications consistent with
     implementations and informal and semi-formal system
     specifications (such as requirements), we use and build tools
     based upon underlying theories of refinement.  Some of these
     foundations are summarized in our paper 
     "[Ensuring Consistency between Designs, Documentation, Formal Specifications, and Implementations](Ensuring_Consistency_between_Designs_Documentation.pdf)."

* Tools and Technologies

  9. For the projects we are running now we are obligated to use
     verifiable, secure C code as our implementation language.  Thus,
     we are using tools like [Cryptol](https://cryptol.net/), 
     [SAW](https://saw.galois.com/), 
     [Frama-C](https://frama-c.com/), and 
     [CBMC](http://www.cprover.org/cbmc/) to
     formally assure that our code conforms to its (Cryptol and 
     [ACSL](https://frama-c.com/acsl.html))
     specifications.  You will find Clafer, Lando, BON, and Cryptol
     specifications in the 
     [specs directory](../../specs/) 
    of the BESSPIN Voting System project.  You will find ACSL
     specifications throughout the 
     [source directory](../../source/) 
     of the project.
