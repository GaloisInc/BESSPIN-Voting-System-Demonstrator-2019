#!/bin/bash
IP=10.88.88.2
curl http://$IP/sim/paper_in_pressed
read
curl http://$IP/sim/scan_barcode_1
read
curl http://$IP/sim/press_button_cast
read
curl http://$IP/sim/paper_in_released
echo "Done"

