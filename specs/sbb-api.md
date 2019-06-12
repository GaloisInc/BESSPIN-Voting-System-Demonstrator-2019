# Smart Ballot Box API

## Global Config

* Feed Timeout (seconds) - Time allowed for paper to feed past the scanner
* Eject Timeout (seconds) - Time allowed for paper to eject
* Cast Timeout (seconds) - Time allowed for paper to finish feededing into BB 
    when ```cast_ballot()``` is called 

## Devices

 * Paper input sensor (INPUT) Active High
 * Paper exit sensor (INPUT) Active High
 * Cast Button LED (OUTPUT) Active Low
 * Cast Button Switch (INPUT) Active High
 * Spoil Button LED (OUTPUT) Active Low
 * Spoil Button Switch (INPUT) Active High
 * Feed Motor (OUTPUT)
    * FWD - P1 HIGH / P2 LOW
    * REV - P2 HIGH / P1 LOW
 * Barcode Scanner UART
 * SD Card SPI
 * 16x2 LCD Dispaly w/ RGB Backlight I2C

## SBBError Codes
```
0 = Success
10 = I2C Init Failure
20 = SD Init Failure
30 = GPIO Init Failure
100 = Feed Timeout
101 = Eject Timeout
102 = Cast Timeout
110 = Invalid State
200 = No Barcode
201 = Invalid Barcode / Ballot
254 = Unknown Error
```
# int sys_check()
  * Returns SBBError
# int feed_paper()
  * Returns SBBError
# int validate_ballot()
  * Returns SBBError
# int user_vote_prompt()
  * Returns SBBError
# int spoil_ballot()
  * Returns SBBError
# int cast_ballot()
  * Returns SBBError
# int eject_paper()
  * Returns SBBError
# void abort()
