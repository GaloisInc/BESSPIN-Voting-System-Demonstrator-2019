/**
 * \file base64.h
 *
 * \brief RFC 1521 base64 encoding/decoding
 */
/*
 *  Copyright (C) 2006-2015, ARM Limited, All Rights Reserved
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Licensed under the Apache License, Version 2.0 (the "License"); you may
 *  not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  This file is part of mbed TLS (https://tls.mbed.org)
 */


/* Additional notes for Galois BSV Project
 *
 * This implementation has been adapted from the mbedTLS module, with the
 * following changes:
 *
 * 1. Frama-C/ACSL contracts have been added here to encode the
 *    reqired relationship between the sizes of the source and destination
 *    buffers.
 * 2. Calls to the assert() macro have also been added to check the
 *    pre- and post-condition at run-time, where possible.
 * 3. Changed to use RFC 4648 "Filename safe" encoding for values 62 and 63
 * 4. Addition of the "add_null" Boolean parameter on mbedtls_base64_encode()
 *    so it can be used safety with binary (not zero-terminated C String)
 *    output buffers.
 */

#ifndef MBEDTLS_BASE64_H
#define MBEDTLS_BASE64_H

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <stdio.h>
#include "base64.acsl"

#define MBEDTLS_ERR_BASE64_BUFFER_TOO_SMALL               -0x002A  /**< Output buffer too small. */
#define MBEDTLS_ERR_BASE64_INVALID_CHARACTER              -0x002C  /**< Invalid character in input. */


/**
 * \brief          Encode a buffer into base64 format
 *
 * \param dst      destination buffer
 * \param dlen     size of the destination buffer
 * \param olen     number of bytes written
 * \param src      source buffer
 * \param slen     amount of data to be encoded
 * \param add_null if true, append final \0 byte to the output
 *
 * \return         0 if successful, or MBEDTLS_ERR_BASE64_BUFFER_TOO_SMALL.
 *                 *olen is always updated to reflect the amount
 *                 of data that has (or would have) been written.
 *                 If that length cannot be represented, then no data is
 *                 written to the buffer and *olen is set to the maximum
 *                 length representable as a size_t.
 *
 * \note           Call this function with dlen = 0 to obtain the
 *                 required buffer size in *olen
 */

/**
 * Additional notes for Galois BSV Project and Frama-C users
 *
 * If add_null == true, then this function adds a
 * final 0x00 byte to the encoded string,
 * so it can be treated as a zero-terminated "C String". This means
 * that dlen is larger than expected, as defined in the requires clause
 * below.
 *
 * The "src" data is arbitrary data, so might contain one or more 0x00 bytes.
 * Therefore the slen parameter must give the exact number of bytes to be encoded.
 */

/*@ requires \valid_read (src + (0 .. slen - 1));
  @ requires \valid (dst + (0 .. dlen - 1));
  @ requires \separated (dst, src, olen);
  @ requires dlen == (((slen % 3) == 0) ? (4 * (slen / 3)) : (4 * ((slen / 3) + 1))) + 2;
  @ assigns dst[0 .. dlen - 1];
  @ assigns *olen;
  @ ensures *olen == (dlen - 2);
*/
int mbedtls_base64_encode (unsigned char *dst,
                           size_t dlen,
                           size_t *olen,
                           const unsigned char *src,
                           size_t slen,
                           bool add_null);





/**
 * \brief          Decode a base64-formatted buffer
 *
 * \param dst      destination buffer (can be NULL for checking size)
 * \param dlen     size of the destination buffer
 * \param olen     number of bytes written
 * \param src      source buffer
 * \param slen     amount of data to be decoded
 *
 * \return         0 if successful, MBEDTLS_ERR_BASE64_BUFFER_TOO_SMALL, or
 *                 MBEDTLS_ERR_BASE64_INVALID_CHARACTER if the input data is
 *                 not correct. *olen is always updated to reflect the amount
 *                 of data that has (or would have) been written.
 *
 * \note           Call this function with *dst = NULL or dlen = 0 to obtain
 *                 the required buffer size in *olen, in which case the
 *                 return value is MBEDTLS_ERR_BASE64_BUFFER_TOO_SMALL
 */

/**
 * Additional notes for Galois BSV Project and Frama-C users
 *
 * slen should be the number of base64 encoded characters to be decoded, but
 * not including any final 0x00 byte. slen must be an exact multiple of 4.
 *
 * The resulting data in dst is arbitrary binary,
 * so should not be used with printf() or any other function
 * that expect a zero-terminated string.
 *
 * The destination buffer must be big enough to accomodate the decoded
 * string, but depends no how much padding is in the final sequence. We
 * therefore require dlen to be a safe upper bound, given by 3 * (slen / 4))
 *
 * For example, with slen == 44, this might decode into 31, 32, or 33
 * characters, depending on the padding. We therefore require dlen to be
 * 33 to be on the safe side.
 *
 * The actual number of characters in the decoded string is reported in
 * *olen, which MUST be evaluated by the caller. *olen will lie in the range
 * 0 .. dlen
 */

/*@ requires \valid_read (src + (0 .. slen - 1));
  @ requires (slen % 4) == 0;
  @ requires \separated (dst, src, olen);
  @ assigns *olen;
  @ behavior length_query:
  @   assumes ((dst == NULL) || (dlen == 0));
  @ behavior decode:
  @   assumes (dst != NULL) && (dlen != 0);
  @   requires dlen == (3 * (slen / 4));
  @   requires \valid (dst + (0 .. dlen - 1));
  @   assigns dst[0 .. dlen - 1];
  @   ensures *olen <= dlen;
  @ complete behaviors;
  @ disjoint behaviors;
*/
int mbedtls_base64_decode( unsigned char *dst, size_t dlen, size_t *olen,
                   const unsigned char *src, size_t slen );

#endif /* base64.h */
