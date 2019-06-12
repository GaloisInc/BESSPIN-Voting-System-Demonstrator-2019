TARGET ?= verification

ifeq ($(TARGET),bottom)
include Makefile.bottom
else
ifeq ($(TARGET),verification)
include Makefile.verification
else
$(info unknown target type: $(TARGET) Available types are "bottom" and "verification")
endif
endif
