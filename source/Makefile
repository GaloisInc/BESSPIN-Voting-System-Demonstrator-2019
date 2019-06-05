GCC = gcc

C_SRC = sbb_hw.c sbb.c main_ballot_box.c

PROG = main_ballot_box

OBJS  = $(C_SRC:.c=.o)

all: $(PROG).elf

$(PROG).elf  : $(OBJS) Makefile 
	@echo Linking....
	@$(GCC) -o $@ $(OBJS)
	@echo Completed $@

clean :
	@rm -f $(OBJS)
