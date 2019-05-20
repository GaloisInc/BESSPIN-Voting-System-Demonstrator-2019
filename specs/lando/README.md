# The Lando specification of the BESSPIN Voting System

##Mandatory Outcomes and Artifacts per Subsystem
* a rich LANDO specification of a subsystem includes(not necessarily in order of execution):
   * a complete domain model
      * all necessary concepts, their descriptions, all features (queries and commands), and constraints
      * a set of domain model elements is (relatively) complete if all system requirements and scenarios have no undefined domain terms
   * a complete set of events
      * events are atomic, either external or internal, and inbound or outbound
      * events often, but not always, correspond with component features
      * events sequentially compose to scenarios
      * a set of events is (relatively) complete if, using them, one can specify the set of all system scenarios
   * a rich set of scenarios
      * scenarios are semi-equivalent to use cases or user stories
      * scenarios capture common normal or abnormal behavioral sequential sequences of events realized via programmatic interactions (API calls, messages, etc.) or HCI events (UI interactions)
      * an adequate set of scenarios are the top-of-mind normal and abnormal sequences of events that describe a subsystem well enough that a new reader can understand its common use cases
      * a rich set of scenarios extends an adequate set by including common failure conditions (abnormal behaviors)
      * a complete set of scenarios covers all of a system’s ASM’s transitions (see below)
      * scenarios are (often manually) transformed into subsystem, integration, and system properties that are validated or verified via runtime verification (testing) or formal verification
   * a sound and complete set of requirements
      * requirements capture behavioral and non-behavioral properties that a system must have to be acceptable by a client
      * a set of requirements is sound if it contains no contradictory requirements
      * often one can only identify contradictory requirements by formally mechanizing requirements via a formal domain engineering model and checking their logical consistency
      * a set of requirements is typically deemed complete by client review
   * a complete static architectural model
      * all concepts in the domain model are represented
      * all containment relations are depicted
      * all client-supplier relations are depicted
      * all subtyping relations are depicted
      * all non-trivial equivalence relations and type conversions are depicted
   * a complete development plan grounded in the architecture
      * all subsystems and/or components have
         * identified owners and contributors
         * effort estimates for design, implementation, and assurance work
         * complexity estimates (low, medium, high)
         * risk levels (low, medium, high)
         * mandatory dependencies elucidated
   * a complete dynamic model
      * all subsystems and/or components that have non-trivial dynamic behavior are described using an appropriate precise dynamic modeling mechanism
         * example mechanisms include: FSMs (DFAs and NFAs), grammars, ASMs, Petri Nets, collaboration diagrams, sequence diagrams, BON dynamic diagrams
      * a dynamic model is complete if
         * all non-trivial behaviors of a system are fully represented in a fashion that permits assurance evidence
         * all scenarios describe single traces through a (set of) ASMs
      * for the purposes of this project, we are using Google Draw ASM models and ACSL and/or Cryptol ASM specs for mechanized, verifiable specs
* an implementation that conforms to the aforementioned specification
* an assurance case that provides evidence that the implementation conforms to the specification
* top-level README for the subsystem following the templated conventions provided for the overall project in Markdown

## Scenario from 5/20
*Print a ballot from BMD, and cast it at SBB*

### BMD
*NUC #1*
* Print the ballot 
  * VotingWorks 2D barcode
  * TODO: how many bits?
  * Barcode contains: Timestamp + encoded ballot

### SBB HW
*SSITH CPU*
* (internal) is paper present?
* (internal) feed paper!
* (internal) stop feeding paper!
* was barcode scanned?
* deposit ballot!
* what is the barcode?

### SBB
*SSITH CPU*
* Perform Tally!
* Is barcode valid?

### Logging
*SSITH CPU*
* Log scanned barcode!
* Log validity check!
* Log tally!
* Log boot status!
* Log ballot deposited!
* Publish Log!

### Reporting
*NUC #2*
* Display the results!