/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

// General includes

// Subsystem includes
#include "crypto.h"

// Constant definitions for the crypto subsystem for the current red
// teamed version of the BVS.

// @note AES only supports 128-bit blocks regardless of key size.
const uint32_t AES_BLOCK_SIZE  = 128; 
const uint32_t AES_KEY_SIZE    = 256;
const uint32_t SHA_DIGEST_SIZE = 256;
