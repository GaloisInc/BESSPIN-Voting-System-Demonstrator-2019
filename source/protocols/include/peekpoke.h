#ifndef PEEK_POKE_H
#define PEEK_POKE_H
#include "FreeRTOS_TCP_server.h"
#include "FreeRTOS_server_private.h"

extern void peekPokeServerTaskPriority( UBaseType_t uxPriority );

extern void peekPokeServerTaskCreate( void );

extern size_t peekPokeHandler( HTTPClient_t *pxClient, BaseType_t xIndex, const char *pcURLData, char *pcOutputBuffer, size_t uxBufferLength );

#endif
