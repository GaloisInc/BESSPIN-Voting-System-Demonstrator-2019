#include "log.h"
#include <stdio.h>
#include <stdlib.h>
int main(void)
{
    // Logging Test 7
    //
    // This test demonstrates that writing two log files in sequence produces identical
    // results to writing the same data to two log file in parallel. This confirms that
    // the handling of the "previous_hash" attribute of the log file is correct.

    // Let the following shorthand apply:
    //  c lx   - create log file lx
    //  w lx d - write data d to log file lx

    // Now imagine we write log file l1 then log file l2 in sequence, thus:
    //   c l1, w l1 m1, w l1 m2, c l2, w l2 m3, w l2 m4
    // Now imagine that we create both l3 and l4, and write the same data to
    // both of them in parallel:
    //   c l3, c l4, w l3 m1, w l4 m3, w l3 m2, w l4 m4
    // If all if well, then log files l1 and l3 will be identical
    // AND l2 and l4 will be identical

    Log_Handle l1, l2, l3, l4;
    ;

    const log_entry m1 =
        "hello "
        "test71xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    const log_entry m2 =
        "hello "
        "test72xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    const log_entry m3 =
        "hello "
        "test73xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    const log_entry m4 =
        "hello "
        "test74xxxxaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbccccccccccccccccdddddddddddd"
        "ddddeeeeeeeeeeeeeeeeffffffffffffffffgggggggggggggggghhhhhhhhhhhhhhhhii"
        "iiiiiiiiiiiiiijjjjjjjjjjjjjjjjkkkkkkkkkkkkkkkkllllllllllllllllmmmmmmmm"
        "mmmmmmmmnnnnnnnnnnnnnnnnooooooooooooooo"; // 256 chars including final \0

    // initialize create log write entry
    Log_IO_Initialize();

    // L1
    create_log(&l1, "test7l1.txt");
    write_entry(&l1, m1);
    write_entry(&l1, m2);
    Log_IO_Close(&l1);

    // L2
    create_log(&l2, "test7l2.txt");
    write_entry(&l2, m3);
    write_entry(&l2, m4);
    Log_IO_Close(&l2);

    // Now L3 and L4 in parallel
    create_log(&l3, "test7l3.txt");
    create_log(&l4, "test7l4.txt");
    write_entry(&l3, m1);
    write_entry(&l4, m3);
    write_entry(&l3, m2);
    write_entry(&l4, m4);
    Log_IO_Close(&l3);
    Log_IO_Close(&l4);

    // NOW... check that test7l1.txt and test7l3.txt are identical AND
    //              that test7l2.txt and test7l4.txt are identical
}
