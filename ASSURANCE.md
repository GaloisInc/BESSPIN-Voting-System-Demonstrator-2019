# Static and Runtime Assurance based on formal verification of the BESSPIN Voting System

Assurance case spans multiple specification languages and tools 
that we use in  BESSPIN Voting System (BVS) project in order to satisfy 
requirements and specify subsystem components, data-types, runtime verification 
and correctness properties.

# Current status

Based on the requirements that every secure component in BVS must have cryptographic integrity
and all cryptographic operations used by submodules must have formal assurance available, 
our formal work has mostly been done in Cryptol, a domain specific language tailored for 
cryptographic algorithms and tool SAW, which leverages mathematical solvers, finding counterexamples 
when program code does not agree with its specification. 
The whole work in Cryprol has been completed and can be seen in cryptol folder.

For static assurance we use platform frama-c, a modular static analysis framework for the C language, 
to assure expectation based on a contract design written in ACSL and to provide an algebraic specification 
either by extracting Cryptol specification or by formally describing some mission critical parts of the system 
in the top-to-bottom style of the formal description. 
This work has been partially done.

In this phase, we have covered all methods with preconditions and postconditions seamlessly refactoring 
code to be much more compliant with frama-c Eva plugin. We put an effort into algebraic specification trying 
to describe the crypto submodule in order to find equivalence relations induced by the cryptographic properties.
This is still an ongoing work in progress.
  
In parallel to this formal verification activity, unit tests have been derived from the specifications, by 
sliceing technique providing both types: regular and malicious tests for all submodules.   
The reason for theadditional testing effort is of course, that unit testing is well-established in the 
software quality dynamic assurance process of safety critical systems. Various tests can be seen in logging,
sbb and protocols submodules.

# Future work

In future we expect to finish the following specifications:
- base64.acsl
- secure_log.acsl
- extended contracts for the AES specific functions
- global and typed invariances based on algebraic specification







