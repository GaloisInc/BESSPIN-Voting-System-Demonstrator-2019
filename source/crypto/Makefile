TARGET ?= bottom

ifeq ($(TARGET),bottom)
include Makefile.bottom
else
# ifeq ($(TARGET),freertos)
# include Makefile.freertos
# else
ifeq ($(TARGET),verification)
include Makefile.verification
else
ifeq ($(TARGET),hosttests)
include Makefile.hosttests
else
$(info unknown target type: $(TARGET) Available types are "bottom", "verification")
endif
endif
endif
#endif
