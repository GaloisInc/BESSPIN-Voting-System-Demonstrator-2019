TARGET ?= verification

ifeq ($(TARGET),bottom)
include Makefile.bottom
else
ifeq ($(TARGET),freertos)
include Makefile.freertos
else
ifeq ($(TARGET),hosttests)
include Makefile.hosttests
else
ifeq ($(TARGET),verification)
include Makefile.verification
else
$(info unknown target type: $(TARGET) Available types are "bottom", "freertos" and "verification")
endif
endif
endif
