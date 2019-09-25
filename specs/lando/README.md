# The Lando specification of the BESSPIN Voting System

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
