/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

// General includes

// Subsystem includes
#include "crypto.h"

// constant definitions for the crypto subsystem
// Note: AES only supports 128-bit blocks regardless of key size
const uint32_t AES_BLOCK_SIZE  = 128; 
const uint32_t AES_KEY_SIZE    = 256;
const uint32_t SHA_DIGEST_SIZE = 256;
