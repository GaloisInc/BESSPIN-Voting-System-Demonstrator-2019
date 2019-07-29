TARGET ?= bottom
$(info TARGET=$(TARGET))

# List all substems directories
SOURCE_DIR = source
SBB_DIR = $(SOURCE_DIR)/sbb
LOG_DIR = $(SOURCE_DIR)/logging
CRYPTO_DIR = $(SOURCE_DIR)/crypto

#####################################
#
# 		SBB Target
#
#####################################


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
clean: crypto_bottom_clean log_bottom_clean

else
#####################################
#
# 		FREERTOS targets
#
#####################################
ifeq ($(TARGET),freertos)
# Common includes
include source/Makefile.freertos_common

freertos_all: freertos_crypto freertos_log freertos_sbb

clean: clean_crypto clean_log clean_sbb

freertos_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos all

clean_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos clean

freertos_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos all

clean_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos clean

freertos_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos all

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

# Assume clang is on PATH, but needs some special setup on Darwin to override
# Apple's clang and use the HomeBrew one instead...
export CC := clang

HOSTTEST_CFLAGS = -g -Wall -DNO_MEMSET_S -DDEBUG -DNETWORK_LOGS -Wno-macro-redefined -fsanitize=address

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
# Common includes
include source/Makefile.freertos_common

sim_all: sim_crypto sim_log sim_sbb

clean: clean_crypto clean_log clean_sbb

sim_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim all

clean_crypto:
	cd $(CRYPTO_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim clean

sim_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim all

clean_log:
	cd $(LOG_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim clean

sim_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim all

clean_sbb:
	cd $(SBB_DIR) ; \
	$(MAKE) -f Makefile.freertos_sim clean


else
$(info unknown target type: $(TARGET) Available types are "bottom", "verification", "freertos", "hosttests")
endif # ($(TARGET),sim)
endif # ($(TARGET),hosttests)
endif # ($(TARGET),verification)
endif # ($(TARGET),freertos)
endif # ($(TARGET),bottom)
