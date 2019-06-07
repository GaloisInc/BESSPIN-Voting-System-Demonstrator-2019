// Temporary fix - defines "uxrandom" function
#include "rand.h"

UBaseType_t ulNextRand = 0;

UBaseType_t uxRand(void)
{
	const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

	/* Utility function to generate a pseudo random number. */
	ulNextRand = (ulMultiplier * ulNextRand) + ulIncrement;
	return ((int)(ulNextRand >> 16UL) & 0x7fffUL);
}
