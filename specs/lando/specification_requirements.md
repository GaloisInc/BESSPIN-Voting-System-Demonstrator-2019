# Specification Requirements for the BESSPIN Voting System

*Joe Kiniry, June 2019*

For every subsystem under development, which includes the top-level
SBB system, there are a number of mandatory outcomes and artifacts to
call that subsystem "done".  Those artifacts and their utility for
assurance are enumerated below.

## A Rich Lando Specification of the Subsystem

A *rich* specification includes (not necessarily in order of creation):
  1. a *complete* **domain model**
     * all necessary **concepts**, their descriptions, all features
       (queries and commands), and constraints
     * a set of domain model elements is (relatively) complete if all
       system requirements and scenarios have no undefined domain
       terms
  2. a *complete* set of **events**
      * events are atomic, either external or internal, and inbound or
        outbound
      * events often, but not always, correspond with component features
      * events sequentially compose to scenarios
      * a set of events is (relatively) complete if, using them, one
        can specify the set of all system scenarios
  3. a *rich* set of **scenarios**
      * scenarios are semi-equivalent to use cases or user stories
      * scenarios capture common normal or abnormal behavioral
        sequential sequences of events realized via programmatic
        interactions (API calls, messages, etc.) or HCI events (UI
        interactions)
      * an *adequate* set of scenarios are the top-of-mind normal and
        abnormal sequences of events that describe a subsystem well
        enough that a new reader can understand its common use cases
      * a *rich* set of scenarios extends an adequate set by including
        common failure conditions (abnormal behaviors)
      * a *complete* set of scenarios covers all of a system’s ASM’s
        transitions (see below)
      * scenarios are (often manually) transformed into subsystem,
        integration, and system properties that are validated or
        verified via runtime verification (testing) or formal
        verification
  4. a *sound* and *complete* set of **requirements**
      * requirements capture behavioral and non-behavioral properties
        that a system must have to be acceptable by a client
      * a set of requirements is *sound* if it contains no
        contradictory requirements
      * often one can only identify contradictory requirements by
        formally mechanizing requirements via a formal domain
        engineering model and checking their logical consistency
      * a set of requirements is typically deemed *complete* by client
        review
  5. a *complete* **static architectural model**
      * all concepts in the domain model are represented
      * all containment relations are depicted
      * all client-supplier relations are depicted
      * all subtyping relations are depicted
      * all non-trivial equivalence relations and type conversions are
        depicted
  6. a *complete* development plan grounded in the architecture
      * all subsystems and/or components have
         * identified *owners* and *contributors*
         * *effort estimates* for *design*, *implementation*, and
            *assurance* work
         * *complexity* estimates (low, medium, high)
         * *risk* levels (low, medium, high)
         * mandatory dependencies elucidated
  7. a *complete* **dynamic model**
      * all subsystems and/or components that have non-trivial dynamic
        behavior are described using an appropriate precise dynamic
        modeling mechanism
         * example mechanisms include: FSMs (DFAs and NFAs), grammars,
           ASMs, Petri Nets, collaboration diagrams, sequence
           diagrams, BON dynamic diagrams
      * a dynamic model is *complete* if
         * all non-trivial behaviors of a system are fully represented
           in a fashion that permits assurance evidence
         * all scenarios describe single traces through a (set of) ASMs
      * for the purposes of this project, we are using Google Draw ASM
        models and ACSL and/or Cryptol ASM specs for mechanized,
        verifiable specs

* a *rich* set of **ACSL contracts** for all code for which an
  assurance case is mandatory

  1. ACSL contracts are both code-level annotations that describe type
     and data invariants and function contracts (including frame
     conditions and exceptional behavior), and
  2. ACSL axiomatic models for all data types for which such a model is
     reasonable and natural and, if such an axiomatic model is
     introduced,
  3. a set of invariants that relate such models to the source code
     (both types and functions)

* a *complete* **Cryptol specification** for all code that relates to
  cryptographic operations (algorithms or protocols)

  1. a *complete* spec includes a reasonable set of Cryptol properties
     that have a documented level of assurance by virtue of some
     combination of the use of runtime random testing or SAT/SMT
     solving, and
  2. a **SAW script** for every verifiable relation between the Cryptol
     specification and the code

* an **implementation** that conforms to the aforementioned specification
  1. conformance means that the code is type-correct wrt the ACSL specs, and
  2. the code has a documented assurance case whose strength is born
     out by the sequel
  
* an **assurance case** that provides evidence that the implementation
  rigorously conforms to the specification, which means one or more of
  the following outcomes

  1. ACSL specifications are type-correct (typecheck)
  2. the implementation has no undefined behavior (EVA)
  3. the implementation has dynamic assurance (RTE)
  4. the implementation has full-functional verification against the
     ACSL (wp)
  5. the implementation has full-functional verification against the
  Cryptol (via SAW)

* a **top-level README.md** for the subsystem following the templated
  conventions provided for the overall project in Markdown

