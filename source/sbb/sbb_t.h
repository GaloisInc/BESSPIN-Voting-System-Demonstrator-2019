/**
 * Smart Ballot Box types
 * @refine sbb.lando
 */

#ifndef __SBB_T__
#define __SBB_T__

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#define BARCODE_MAX_LENGTH 16

typedef char* barcode;
// @todo kiniry Add a pure helper function for relating
// BARCODE_MAX_LENGTH to all uses of the pair (barcode,
// barcode_length).
typedef uint8_t barcode_length;
// @review kiniry Should we introduce a string type?
typedef char* string;

#endif
