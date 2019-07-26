#!/bin/bash
GFE_REPO_PATH=../gfe
# make the ballot box binary
make clean; make;
# copy the binary to the GFE
cp main_ballot_box.elf $GFE_REPO_PATH/bootmem/freertos.elf
#Making the FreeRTOS binary image <bootmem.bin>
cd $GFE_REPO_PATH/bootmem
make -f Makefile.freertos clean
make -f Makefile.freertos
cd ..
# run the simple upload flash script
./upload_flash_simple.sh chisel_p1