## Ballot Box ASM

  * ### SysCheck
    * Pre Conditions
        * Power applied, switched on
    * Post Conditions
        * I2C display initialized.  Backlight Off. Text Displayed??
        * GPIO Initialized, inputs / outputs configured
        * SPI / SDCard Initialized, read check performed
    * Error Conditions
        * I2C initialization failure -> (abort)
        * SPI / SD initialization / read failure -> (abort)
        * Initial GPIO state unexpected. -> (abort)
           * Paper insertetd on boot?
           * Buttons pressed?
  * ### ReadyWait
    * Pre Conditions
      * IO Interfaces initialized 
      * Feed / Eject timeout timer reset
      * Paper input sensor off LOW
        * This is important after an eject.  May require the user to physicaly remove the paper and re-insert it.
      * Paper output sensor off LOW
      * Button LEDs off
      * Display Backlight off?
    * Post Conditions
      * None
  * ### FeedPaper
    * Pre Conditions
      * Paper Input Sensor depressed (HIGH)
      * Paper Feed timer active
      * Feed motor active FWD
    * Post Conditions
      * Paper Input Sensor unpressed (LOW)
      * Paper Output Sensor triggered (HIGH)
      * Feed motor inactive
    * Error Conditions
      * Feed timeout timer reached -> (eject)
      * No Barcode detected -> (eject)
      * Invalid Barcode -> (eject)
  * ### PromptUser
    * Pre Conditions
      * Last State was FeedPaper
      * Paper Input sensor off LOW
      * Paper Output sensor on HIGH
      * I2C Display backlight on
      * User prompt displayed cast/spoil
      * User button LEDS on
    * Post Condition
      * Cast button pressed -> (UserSpoil)
      * Spoil button pressed -> (UserCast)
  * ### UserSpoil
    * Pre Conditions
      * Spoil button pressed
      * Paper Output sensor triggered HIGH
    * Post Conditions
      * -> (EjectPaper)
  * ### UserCast
    * Pre Conditions
       * Cast button pressed 
       * Paper output sensor triggered HIGH
       * Feed motor drive FWD
    * Post Conditions
      * Paper outputt sensor LOW
      * -> (ReadyWait)
      
  * ### EjectPaper
    * Pre Condition
    * Post Condition
      * Paper output sensor off LOW
      * Paper inputt sensor off HIGH
    * Error Conditions
      * Eject Paper Timeout
  * ### Abort
     * Pre Condition
       * Any other state reached Error Condition without retry
    * Post Condition
       * Display shows error message
       * GPIO Disabled
       * System requires reboot to resume state machine