# Log Messages

The following are descriptions of the messages written to the app and system
logs. The format of these messages is _in addition to_ whatever format the log
subsystem imposes on messages.

## App Log

An app message is:

 * `"0 <QR-Code>"` denoting a the ballot with QR code `<QR-Code>` was cast.
 * `"1 <QR-Code>"` denoting a the ballot with QR code `<QR-Code>` was spoiled.
 
The QR-Code format is defined elsewhere, but is currently a 16-byte timestamp
and a 44 byte Base64-encoded message.

## System Log

A system log message is one of:

* `"State change: <fld> := <val>"`, denoting a HW state change or logical state change. `<fld>` is one of the field names of `SBB_state` defined in `sbb_t.h`, and `<val>` is the _name_ of the new value of the field (i.e., the enum val, like `SPOIL` or `PAPER_DETECTED`).

* A HW event message:

    * `"Sensor in pressed"`
    * `"Sensor in released"`
    * `"Sensor out pressed"`
    * `"Sensor out released"`
    * `"Cast button pressed"`
    * `"Cast button released"`
    * `"Spoil button pressed"`
    * `"Spoil button released"`
    * `"Barcode scanned"`
    * `"Received barcode"`
    * `"Received empty barcode"`

* A special message denoting the reason for a transition

    * `"Barcode is invalid"`
    * `"User cast/spoil decision timeout"`
