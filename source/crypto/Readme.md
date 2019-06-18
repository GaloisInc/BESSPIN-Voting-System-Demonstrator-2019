BVS Crypto Subsystem
====================

This subsystem supplies cryptographics primitives supporting the BVS.

Top-Level API
-------------

This appears in crypto.h

This API should be used by all other BVS subsystems

Current algorithms and implementations
======================================

AES (Software)
--------------

The units aes.c, cbc.c, and mode_wrappers.c are an all-software implementation of AES, supporting a standard AES block size of 128 bits, various standard key lengths, and various block encryptions modes.

These units are adapted from the OpenSSL reference implementation.

SHA2-256 (Software)
-------------------

TBD


