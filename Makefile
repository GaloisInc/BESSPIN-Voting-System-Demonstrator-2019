TARGET ?= bottom
$(info TARGET=$(TARGET))

# List all substems directories
export SOURCE_DIR = $(PWD)/source
export SBB_DIR = $(SOURCE_DIR)/sbb
export LOG_DIR = $(SOURCE_DIR)/logging
export CRYPTO_DIR = $(SOURCE_DIR)/crypto
export INCLUDE_DIR = $(SOURCE_DIR)/include

# Expected GFE repo location (for flash scripts)
CURRENT_PATH=$(shell pwd)
GFE_DIR ?= $(CURRENT_PATH)/../gfe
P1_BITSTREAM_PATH ?= $(GFE_DIR)/bitstreams/soc_chisel_p1.bit

# To enable the running lights task
export USE_LED_BLINK_TASK=1
#####################################
#
# 		SBB Target
#
#####################################
fpga:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos default
	cp $(SBB_DIR)/default_ballot_box.* .

sim:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim default
	cp $(SBB_DIR)/default_ballot_box_sim.* .

clean_all:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos clean
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim clean
	rm -f default_ballot_box.*
	rm -f default_ballot_box_sim.*

#####################################
#
# 		BOTTOM targets
#
#####################################
ifeq ($(TARGET),bottom)

include $(SBB_DIR)/Makefile.bottom
include $(CRYPTO_DIR)/Makefile.bottom
include $(LOG_DIR)/Makefile.bottom

bottom_all: crypto_bottom log_bottom sbb_bottom
clean: crypto_bottom_clean log_bottom_clean sbb_bottom_clean

else
#####################################
#
# 		POSIX targets
#
#####################################
ifeq ($(TARGET),posix)
export CC := clang
export CFLAGS := -DVOTING_PLATFORM_POSIX -fsanitize=address
export OS_DIR = $(SOURCE_DIR)/os/posix
posix_all: posix_crypto posix_log posix_sbb

clean: clean_crypto clean_log clean_sbb

posix_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.posix default

posix_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.posix default

posix_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.posix default

clean_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.posix clean

clean_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.posix clean

clean_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.posix clean

else
#####################################
#
# 		FREERTOS targets
#
#####################################
ifeq ($(TARGET),freertos)

freertos_all: freertos_crypto freertos_log freertos_sbb

clean: clean_crypto clean_log clean_sbb

freertos_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos default

clean_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos clean

freertos_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos default

clean_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos clean

freertos_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos default

clean_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos clean

else
#####################################
#
# 		VERIFICATION targets
#
#####################################
ifeq ($(TARGET),verification)

typecheck_all: typecheck_crypto typecheck_sbb typecheck_log

verify_all: verify_crypto verify_sbb verify_log

clean: clean_crypto clean_sbb clean_log

typecheck_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.verification typecheck

verify_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.verification verify

clean_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.verification clean


typecheck_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.verification typecheck

verify_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.verification verify

clean_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.verification clean

typecheck_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.verification typecheck

verify_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.verification verify

clean_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.verification clean

else
#####################################
#
# 		HOSTTESTS targets
#
#####################################
ifeq ($(TARGET),hosttests)
export OS_DIR = $(SOURCE_DIR)/os/freertos

# Assume clang is on PATH, but needs some special setup on Darwin to override
# Apple's clang and use the HomeBrew one instead...
export CC := clang

HOST  := $(shell uname -s)
ifeq (${HOST},Linux)
    LLVM_LINK := /usr/lib/llvm-7/bin/llvm-link
    PLATFORM_INCLUDES = -I/usr/include
else
    # Assumed to be Host = Darwin
    LLVM_LINK := llvm-link
    PLATFORM_INCLUDES = -I/usr/include
endif

INCLUDES = $(PLATFORM_INCLUDES) \
           -I $(INCLUDE_DIR)

HOSTTEST_CFLAGS = -g -Werror -Wall -DVOTING_PLATFORM_POSIX -DNO_MEMSET_S -DVOTING_SYSTEM_DEBUG -DNETWORK_LOGS -DLOG_SYSTEM_DEBUG -Wno-macro-redefined $(INCLUDES)

include $(CRYPTO_DIR)/Makefile.hosttests
include $(LOG_DIR)/Makefile.hosttests
include $(SBB_DIR)/Makefile.hosttests

hosts_all: crypto_hosttest_all log_hosttest_all sbb_hosttest_all
clean: crypto_hosttest_clean log_hosttest_clean sbb_hosttest_clean

else
#####################################
#
# 		SIMULATION targets
#
#####################################
ifeq ($(TARGET),sim)
export OS_DIR = $(SOURCE_DIR)/os/freertos
export CFLAGS := -DVOTING_PLATFORM_FREERTOS

sim_all: sim_crypto sim_log sim_sbb

clean: clean_crypto clean_log clean_sbb

sim_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim default

clean_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim clean

sim_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim default

clean_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim clean

sim_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim default

clean_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim clean

else
#####################################
#
# 		DEPLOYMENT targets
#
#####################################
ifeq ($(TARGET),deploy)
all_boxes:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos all
	cp $(SBB_DIR)/default_ballot_box.* .
	cp $(SBB_DIR)/ballot_box_* .

upload_binary_box1: all_boxes
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/ballot_box_1.elf --no-bitfile

upload_binary_box2: all_boxes
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/ballot_box_2.elf --no-bitfile

upload_binary_box3: all_boxes
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/ballot_box_3.elf --no-bitfile

upload_binary_box4: all_boxes
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/ballot_box_4.elf --no-bitfile

upload_binary_sim: sim
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/default_ballot_box_sim.elf --no-bitfile

upload_binary_and_bitstream_sim: sim
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/default_ballot_box_sim.elf

upload_binary_fpga: fpga
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/default_ballot_box.elf --no-bitfile

upload_binary_and_bitstream_fpga: fpga
	@echo GFE_DIR=$(GFE_DIR)
	@echo CURRENT_PATH=$(CURRENT_PATH)
	@echo P1_BITSTREAM_PATH=$(P1_BITSTREAM_PATH)
	cd $(GFE_DIR);  \
	./upload_flash_simple.sh $(P1_BITSTREAM_PATH) $(CURRENT_PATH)/default_ballot_box.elf

endif # ($(TARGET),deploy)
endif # ($(TARGET),sim)
endif # ($(TARGET),hosttests)
endif # ($(TARGET),verification)
endif # ($(TARGET),linux)
endif # ($(TARGET),freertos)
endif # ($(TARGET),bottom)
