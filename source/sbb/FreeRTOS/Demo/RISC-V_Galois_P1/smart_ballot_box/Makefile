# Makefile for Building the "bottom" variant of the BVS application

.PHONY: bottom bottom_clean

# Assume clang is on PATH, but needs some special setup on Darwin to override
# Apple's clang and use the HomeBrew one instead...
export CC := clang

# Build the bottom target
bottom:
	$(CC) sbb_main.c sbb_bottom.c -o sbb_bottom.elf
	rm -f *.o

bottom_clean:
	rm sbb_bottom.elf
