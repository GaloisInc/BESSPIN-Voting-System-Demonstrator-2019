#!/bin/bash
CURRENT_PATH='pwd'
GFE_REPO_PATH=../gfe
# make the ballot box binary
make clean; make;

cd $GFE_REPO_PATH
# run the simple upload flash script
# takes around 10min to burn bitstream+binary
# around 30s for the binary only
# ./upload_flash_simple.sh chisel_p1  $CURRENT_PATH/main_ballot_box.elf --no-bitstream
./upload_flash_simple.sh chisel_p1  $CURRENT_PATH/main_ballot_box.elf