# Smart Ballot Box Bill of Materials


### Laser Cut Parts

| Qty Req | Description         | On Hand | Ordered | Notes 
|---------|---------------------|---------|---------|-------
| 1       | GFE enclosure back  | 1       | 0       | 24x24"
| 1       | GFE enclosure front | 1       | 0       | 24x24" clear acrylic

### 3D Printed Parts

| Qty Req | Description             | On Hand | Notes       
|---------|-------------------------|---------|-------------
| 1       | UI enclosure            | 1       | Houses buttons and LCD
| 4       | GFE enclosure corners   | 1       | in development
| 1       | GFE enclosure bottom    | 0       | in development
| 1       | GFE enclosure top       | 0       | in development
| 1       | GFE enclosure right     | 0       | in development
| 1       | GFE enclosure left      | 0       | in development
| 1       | Motor Shaft Coupler     | 1       |
| 1       | Paper deflector         | 0       | in development
| 1       | Cable / finger Saver    | 0       |
| 1       | Motor Mount             | 1       |
| 1       | Motor spacer            | 1       | 
| 2       | mag adapter mount       | 1       |
| 1       | Scanner mount           | 1       |


### Electro Mechanical
| Qty Req | Description                  | Vendor        | SKU | Manf | On Hand | Ordered | Notes |
|---------|------------------------------|---------------|-----|------|---------|---------|-------|
| 1       | Paper feeder from printer    |               |
| 1       | Brushed Motor                | Amazon        | 
| 2       | LED Push Button              | Amazon        |
| 1       | Paper In Sensor              | Sparkfun      |
| 1       | Paper Out Sensor             | 
| 1       | 2D Barcode Scanner           | Waveshare     |
| 1       | Ethernet Panel mount conn.   | 
| 1       | USB Panel connector          |
| 1       | SBB Connector board assy     |
| 1       | GFE                          |
| 1       | GFE Power Supply             |
| 1       | MicroSD Card                 | 
| 1       | LR44 Battery                 |                |  |  |   Lots! | |

### Wires & Cables
| Qty Req | Description                               | Vendor | SKU | Manf | On Hand | Ordered | Notes |
|---------|-------------------------------------------|--------|-----|------|---------|---------|-------|
| 1       | 6 Pin PCIE splitter (modified)            | Amazon |     |      | 3       |         |       |
| 4       | 4 pin JST 18"                             | 
| 2       | 3 pin JST 18" single end (sensors)        |
| 1       | 2 pin Motor wire JS                       |

### Hardware
| Qty Req | Description                  | On Hand | Ordered | Notes 
|---------|------------------------------|---------|---------|-----------------------------------
| 1       | Modified file cabinet        | 2       |         | Could be swapped out for other box
| 15      | M2x10                        |         |         | 4 for UX mount and 4 for scanner mount, 4 for lcd, ssb-sheild
| 4       | M2 washers                   |         |         | 4 for UX mount
| 8       | M3x10                        |         |         | scanner & motor mounts
| 4       | M3x20                        |         |         | top draw fasteners
| 4       | M3                           |         |         |  

### Connector Board Assy
| Qty | Value        | Package               | Parts                                           | Description          | On Hand | Ordered
|-----|--------------|-----------------------|-------------------------------------------------|----------------------|---------|---------
| 1   |              | C0603K                | C1                                              | CAPACITOR
| 1   |              | C0805K                | C7                                              | CAPACITOR, American symbol
| 1   |              | 1X02_2.54_SCREWTERM   | J1                                              |
| 1   |              | MOLEX-1X2_LOCK        | MOTOR1                                          |
| 2   |              | MOLEX-1X3_LOCK        | PAPER_IN, PAPER_OUT                             |
| 4   |              | MOLEX-1X4_LOCK        | CAST_BTN, LCD, SCANNER1, SPOIL_BTN              |
| 1   |              | PANASONIC_D           | C6                                              |
| 1   | 32.768k      | TC26H                 | Q2                                              | CRYSTAL
| 4   |              | SOT-23                | T3, T4, T5, T6                                  | N CH MOS FET
| 2   |              | 2X06                  | PMOD1, PMOD2                                    | PIN HEADER
| 6   |              | R0603                 | R1, R2, R3, R4, R5, R7                          | RESISTOR, American symbol
| 2   | 10k          | TC33X                 | TM1, TM2                                        | SMT trimmer potentiometer part number TC33X
| 2   |              | SOT223                | U2, U4                                          | Voltage Regulator LM1117
| 2   | .1uf         | C0603K                | C9, C12                                         | CAPACITOR, American symbol
| 10  | 10k          | R0603                 | R6, R13, R15, R16, R17, R19, R20, R21, R22, R23 | RESISTOR, American symbol
| 2   | 10pf         | C0603K                | C4, C5                                          | CAPACITOR, American symbol
| 2   | 10uf         | C1206K                | C8, C11                                         | CAPACITOR, American symbol
| 2   | 1k           | R0603                 | R12, R14                                        | RESISTOR, American symbol
| 3   | 1uf          | C0603K                | C2, C3, C10                                     | CAPACITOR, American symbol
| 2   | 220          | R0603                 | R8, R11                                         | RESISTOR, American symbol
| 1   | 30k          | R0603,                | R18                                             | RESISTOR, American symbol
| 1   | 360          | R0603                 | R9                                              | RESISTOR, American symbol
| 1   | 500          | R0603                 | R10                                             | RESISTOR, American symbol
| 1   | DRV8871DDA   | SOIC127P600X170-9N    | IC4                                             |
| 1   | DS1338-33    | SO-8                  | IC1                                             |
| 1   | LM393D       | SO08                  | IC2                                             | COMPARATOR
| 1   | LR44         | LR44                  | BATT1                                           |
| 1   | MICROSD      | MICROSD               | U1                                              | Micro-SD / Transflash card holder with SPI pinout