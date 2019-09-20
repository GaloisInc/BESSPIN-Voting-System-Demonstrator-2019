# BVS OS Subsystem

The OS-dependent (or OSD) subsystem supports the implementations of
the core BVS subsystems (crypto, logging, sbb). This subsystem exposes
OS-agnostic type definitions and procedure implementations.

## API

This appears in [votingdefs.h](../include/votingdefs.h), which is primarily
expected to include the appropriate OSD headers. This is to allow
implementations to supply implementations using the C preprocessor, rather than
forcing each implementation to implement wrappers. This decision can be
revisited, as it is primarily for convenience of implementation.

The current OSD implementations include:

1. A fictional *bottom* OS
2. POSIX (intended to support both macOS and Linux)
3. FreeRTOS
