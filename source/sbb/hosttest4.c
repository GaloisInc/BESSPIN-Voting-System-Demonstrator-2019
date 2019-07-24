#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"

int main(void) {
    // Current time is not OK
    assert(timestamp_lte_now("2019+06+22+11+18"));
    // all digits <= are lt
    assert(timestamp_lte_now("2019+06+22+11+17"));
    assert(timestamp_lte_now("2019+06+22+10+18"));
    assert(timestamp_lte_now("2019+06+21+11+18"));
    assert(timestamp_lte_now("2019+05+22+11+18"));
    assert(timestamp_lte_now("2018+06+22+11+18"));

    assert(timestamp_lte_now("2019+06+22+10+19"));
    assert(timestamp_lte_now("2019+06+21+13+18"));
    assert(timestamp_lte_now("2019+06+05+50+18"));

    assert(!timestamp_lte_now("2019+06+22+11+19"));
    assert(!timestamp_lte_now("2019+06+22+15+12"));
    assert(!timestamp_lte_now("2020+06+22+10+10"));
    assert(!timestamp_lte_now("2019+07+01+01+01"));
    assert(!timestamp_lte_now("2019+06+23+01+01"));
    return 0;
}
