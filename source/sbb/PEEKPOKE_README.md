# FreeRTOS web server & Peek-Poke application

The FreeRTOS distribution we're using didn't include these files, but
they show up in the "Labs" variant of FreeRTOS:

- https://www.freertos.org/FreeRTOS-Labs/downloads/160919_FreeRTOS_Labs.zip

In particular, the `protocols` directory here comes from:
`160919_FreeRTOS_Labs/FreeRTOS-Plus/Source/FreeRTOS-Plus-TCP/protocols`

The original FreeRTOS web server knew how to serve up static files, but from
a filesystem that we (maybe) don't want to support, so all of that is now
gone from the relevant `*HTTP*` files.

## Peek-Poke application server

The files `HTTP/peekpoke.c` and `include/peekpoke.h` define our HTTP request
handler. The server itself is in `HTTP/FreeRTOS_HTTP_server.c` and is
hard-coded to call into the `peekpoke` files.  To launch the web server
task, head up a level and see `demo/main_peekpoke.c`.

Right now, `peekpoke` supports three endpoints:

- `GET /hello`:  prints a suitable *Hello, world* sort of message, including the
  address and size of an on-stack buffer, suitable for buffer exploits and
  such. This will also tell you the maximum number of bytes that can be
  sent in a reply message.

- `GET /peek/[address]/[nbytes]`: goes to the given address in memory, reads
  the given number of bytes, and returns them as an
  `application/octet-stream` (i.e., raw binary stream). Note that the
  address may be specified in hex by preceding it with `0x` or in octal by
  preceding it with `0` (basically, using the support for base-8, -10, and
  -16 from C's `strtol` function). If `nbytes` is greater than a compiled
  constant, then you only get that many bytes.

- `PATCH /poke/[address]/[nbytes]`: takes `nbytes` of additional data from
  the HTTP request and overwrites memory at the requested address. As with
  `/peek`, the address can be base-8, -10, or -16.

### Exercising the PATCH command via curl

Useful to have here because it's not easy to remember:

`echo dcba | curl -T - --request PATCH http://10.88.88.2/poke/0xc00bd190/4`
