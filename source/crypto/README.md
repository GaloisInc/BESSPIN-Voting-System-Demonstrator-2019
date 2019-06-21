BVS Crypto Subsystem
====================

This subsystem supplies cryptographic primitives supporting the BVS.

Top-Level API
-------------

This appears in `crypto.h`.

This API should be used by all other BVS subsystems. Direct access to the lower level implementations (which might change in future) is not permitted.

Current algorithms and implementations
======================================

These algorithms are *all* implemented entirely in software for now, with no demand for any particular hardware support.

Support for Hardware Security Module (HSM) will appear in future.

AES
---

The units `aes.c`, `cbc.c`, and `mode_wrappers.c` are an all-software implementation of AES, supporting a standard AES block size of 128 bits, various standard key lengths, and various block encryption modes.

These units are adapted from the OpenSSL reference implementation.

SHA2-256
--------

The implemenation in sha2-openbsd.c is adapted from the OpenBSD sources. The only change to use the standard C99 integer types (uint8_t etc.) rather than OpenBSD's u_int8_t etc. which are not supported on all our compilers and targets.

AES-CBC-MAC
-----------

Implemented by RCC in crypto.c. Very simple implementation for now. Insists that the length of the input data is an exact multiple of the AES block size (16 bytes), which is sufficient for our needs for the moment.

HMAC
----

This was originally intended to be implemented, but has been abandoned in favour of AES-CBC-MAC
