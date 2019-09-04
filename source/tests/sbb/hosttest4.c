#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sbb_crypto.h"

const uint8_t *timestamp_1 = (const uint8_t *) "2019+06+24+11+18";
const uint8_t *timestamp_2 = (const uint8_t *) "2019+06+24+11+17";
const uint8_t *timestamp_3 = (const uint8_t *) "2019+06+24+10+18";
const uint8_t *timestamp_4 = (const uint8_t *) "2019+06+23+11+18";
const uint8_t *timestamp_5 = (const uint8_t *) "2019+05+24+11+18";
const uint8_t *timestamp_6 = (const uint8_t *) "2018+06+24+11+18";
const uint8_t *timestamp_7 = (const uint8_t *) "2019+06+24+10+19";
const uint8_t *timestamp_8 = (const uint8_t *) "2019+06+21+13+18";
const uint8_t *timestamp_9 = (const uint8_t *) "2019+06+05+50+18";
const uint8_t *timestamp_10 = (const uint8_t *) "2019+06+24+11+19";
const uint8_t *timestamp_11 = (const uint8_t *) "2019+06+24+15+12";
const uint8_t *timestamp_12 = (const uint8_t *) "2020+06+24+10+10";
const uint8_t *timestamp_13 = (const uint8_t *) "2019+07+01+01+01";
const uint8_t *timestamp_14 = (const uint8_t *) "2019+06+25+01+01";

int main(void) {
    // Current time
    assert(timestamp_after_now(timestamp_1));
    // all digits <= are lt
    assert(!timestamp_after_now(timestamp_2));
    assert(!timestamp_after_now(timestamp_3));
    assert(!timestamp_after_now(timestamp_4));
    assert(!timestamp_after_now(timestamp_5));
    assert(!timestamp_after_now(timestamp_6));

    assert(!timestamp_after_now(timestamp_7));
    assert(!timestamp_after_now(timestamp_8));
    assert(!timestamp_after_now(timestamp_9));

    assert(timestamp_after_now(timestamp_10));
    assert(timestamp_after_now(timestamp_11));
    assert(timestamp_after_now(timestamp_12));
    assert(timestamp_after_now(timestamp_13));
    assert(timestamp_after_now(timestamp_14));
    return 0;
}
