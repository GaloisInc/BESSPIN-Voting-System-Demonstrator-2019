#include "FreeRTOS.h"

/* Use by the pseudo random number generator. */
extern UBaseType_t ulNextRand;

UBaseType_t uxRand(void);