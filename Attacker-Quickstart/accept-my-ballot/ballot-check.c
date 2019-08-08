void exploit() {
// 2. check the barcode
    char *barcode_magic_char = (char *)0xc010aaed;
    if (barcode_magic_char[0] == 'F' && barcode_magic_char[1] == 'F'){
        int *jump_to_success = (int *)0xc0025c04;
    } else {
        int *jump_to_failure = (int *)0xc0025aac;
    }
}
