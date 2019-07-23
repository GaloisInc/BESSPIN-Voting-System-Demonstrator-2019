#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"

int main(void) {
    // Current time is OK
    assert(time_is_valid("2019+07+22+13+18"));
    // All digits <= are OK
    assert(time_is_valid("2019+07+22+13+17"));
    assert(time_is_valid("2019+07+22+12+18"));
    assert(time_is_valid("2019+07+21+13+18"));
    assert(time_is_valid("2019+06+22+13+18"));
    assert(time_is_valid("2018+07+22+13+18"));

    // Some digits > than corresponding digits are OK
    assert(time_is_valid("2019+07+22+12+19"));
    assert(time_is_valid("2019+06+22+13+18"));
    assert(time_is_valid("2019+07+05+50+18"));

    assert(!time_is_valid("2019+07+22+13+19"));
    assert(!time_is_valid("2019+07+22+15+12"));
    assert(!time_is_valid("2020+07+22+13+15"));
    assert(!time_is_valid("2019+08+01+01+01"));
    assert(!time_is_valid("2019+07+23+01+01"));
    return 0;
}
