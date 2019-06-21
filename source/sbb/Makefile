TARGET ?= bottom

ifeq ($(TARGET),bottom)
include Makefile.bottom
else
ifeq ($(TARGET),freertos)
include Makefile.freertos
else
ifeq ($(TARGET),verification)
include Makefile.verification
else
ifeq ($(TARGET),hosttests)
all:
	@echo Warning: No hosttests are present
#include Makefile.hosttests
else
$(info unknown target type: $(TARGET) Available types are "bottom", "verification", "freertos", "hosttests")
endif
endif
endif
endif
