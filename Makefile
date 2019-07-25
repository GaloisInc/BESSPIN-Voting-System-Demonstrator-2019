RISCV_XLEN ?= 32
RISCV_LIB  ?= elf
CCPATH =
ARCH 		= -march=rv32im
ABI 		= -mabi=ilp32


TARGET=$(CCPATH)riscv${RISCV_XLEN}-unknown-${RISCV_LIB}

GCC		= $(TARGET)-gcc
OBJCOPY	= $(TARGET)-objcopy
OBJDUMP	= $(TARGET)-objdump
AR		= $(TARGET)-ar
RANLIB	= $(TARGET)-ranlib

FREERTOS_DEMO_DIR = FreeRTOS-mirror/FreeRTOS/Demo/RISC-V_Galois_P1

# Use main_blinky as demo source and target file name if not specified
PROG 	= main_ballot_box
CRT0	= $(FREERTOS_DEMO_DIR)/bsp/boot.S

# For debugging
$(info $$PROG is [${PROG}])

SBB_SOURCE_DIR = source/sbb
LOG_SOURCE_DIR = source/logging
CRYPTO_SOURCE_DIR = source/crypto
FREERTOS_SOURCE_DIR	= FreeRTOS-mirror/FreeRTOS/Source
FREERTOS_PLUS_SOURCE_DIR = FreeRTOS-mirror/FreeRTOS-Plus/Source
FREERTOS_TCP_SOURCE_DIR = $(FREERTOS_PLUS_SOURCE_DIR)/FreeRTOS-Plus-TCP
FREERTOS_PROTOCOLS_DIR = source/protocols



WARNINGS= -Wall -Wextra -Wshadow -Wpointer-arith -Wbad-function-cast -Wcast-align -Wsign-compare \
		-Waggregate-return -Wstrict-prototypes -Wmissing-prototypes -Wmissing-declarations -Wunused


# Root of RISC-V tools installation
RISCV ?= /opt/riscv

FREERTOS_SRC = \
	$(FREERTOS_SOURCE_DIR)/croutine.c \
	$(FREERTOS_SOURCE_DIR)/list.c \
	$(FREERTOS_SOURCE_DIR)/queue.c \
	$(FREERTOS_SOURCE_DIR)/tasks.c \
	$(FREERTOS_SOURCE_DIR)/timers.c \
	$(FREERTOS_SOURCE_DIR)/event_groups.c \
	$(FREERTOS_SOURCE_DIR)/stream_buffer.c \
	$(FREERTOS_SOURCE_DIR)/portable/MemMang/heap_4.c

APP_SOURCE_DIR	= $(FREERTOS_DEMO_DIR)/../Common/Minimal

PORT_SRC = $(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/port.c
PORT_ASM = $(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/portASM.S

INCLUDES = \
	-I$(FREERTOS_DEMO_DIR)/bsp \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx/common \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx/axidma \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx/axiethernet \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550 \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx/spi \
	-I$(FREERTOS_DEMO_DIR)/bsp/xilinx/gpio \
	-I$(FREERTOS_SOURCE_DIR)/include \
	-I$(FREERTOS_DEMO_DIR)/../Common/include \
	-I$(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V \
	-I$(FREERTOS_DEMO_DIR)/demo \
	-I$(FREERTOS_DEMO_DIR)/devices \
	-I$(SBB_SOURCE_DIR) \
	-I$(LOG_SOURCE_DIR) \
	-I$(CRYPTO_SOURCE_DIR)

ASFLAGS  += -g $(ARCH) $(ABI)  -Wa,-Ilegacy \
	-I$(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/chip_specific_extensions/RV32I_CLINT_no_extensions \
	-DportasmHANDLE_INTERRUPT=external_interrupt_handler

CFLAGS = $(WARNINGS) $(INCLUDES)
CFLAGS += -O0 -g3 $(ARCH) $(ABI) -mcmodel=medany
CFLAGS += \
	-DTARGET_OS_FreeRTOS -DNO_MEMSET_S \
	-DVOTING_SYSTEM_DEBUG #-DNETWORK_LOGS #-DSIMULATION
 	#-DHARDCODE_CURRENT_TIME \
    #-DCURRENT_YEAR=2019 \
    #-DCURRENT_MONTH=6 \
    #-DCURRENT_DAY=24 \
    #-DCURRENT_HOUR=21 \
    #-DCURRENT_MINUTE=12

DEMO_SRC = \
	$(SBB_SOURCE_DIR)/main_freertos.c \
	$(SBB_SOURCE_DIR)/sbb_tcp.c \
	$(SBB_SOURCE_DIR)/sbb.c \
	$(SBB_SOURCE_DIR)/sbb_machine.c \
	$(SBB_SOURCE_DIR)/sbb_strings.c \
    $(SBB_SOURCE_DIR)/sbb_logging.c \
    $(SBB_SOURCE_DIR)/sbb_crypto.c \
	$(LOG_SOURCE_DIR)/log.c \
    $(LOG_SOURCE_DIR)/secure_log.c \
    $(LOG_SOURCE_DIR)/system_log.c \
    $(LOG_SOURCE_DIR)/application_log.c \
    $(LOG_SOURCE_DIR)/log_io.c \
    $(LOG_SOURCE_DIR)/log_fs.c \
    $(LOG_SOURCE_DIR)/log_net.c \
    $(LOG_SOURCE_DIR)/debug_io.c \
    $(CRYPTO_SOURCE_DIR)/base64.c \
    $(CRYPTO_SOURCE_DIR)/crypto.c \
    $(CRYPTO_SOURCE_DIR)/sha2-openbsd.c \
    $(CRYPTO_SOURCE_DIR)/aes.c \
    $(CRYPTO_SOURCE_DIR)/cbc.c \
    $(CRYPTO_SOURCE_DIR)/mode_wrappers.c

APP_SRC = \
	$(FREERTOS_DEMO_DIR)/bsp/bsp.c \
	$(FREERTOS_DEMO_DIR)/bsp/plic_driver.c \
	$(FREERTOS_DEMO_DIR)/bsp/syscalls.c \
	$(FREERTOS_DEMO_DIR)/bsp/uart.c \
	$(FREERTOS_DEMO_DIR)/bsp/iic.c \
	$(FREERTOS_DEMO_DIR)/bsp/gpio.c \
	$(FREERTOS_DEMO_DIR)/bsp/spi.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550_g.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550_sinit.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550_selftest.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550_stats.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550_options.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550_intr.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/uartns550/xuartns550_l.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axidma/xaxidma_bd.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axidma/xaxidma_bdring.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axidma/xaxidma.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axidma/xaxidma_selftest.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axidma/xaxidma_g.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axidma/xaxidma_sinit.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axiethernet/xaxiethernet.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axiethernet/xaxiethernet_control.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axiethernet/xaxiethernet_g.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/axiethernet/xaxiethernet_sinit.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic/xiic.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic/xiic_g.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic/xiic_sinit.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic/xiic_selftest.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic/xiic_master.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic/xiic_intr.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/iic/xiic_stats.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/spi/xspi.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/spi/xspi_g.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/spi/xspi_sinit.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/spi/xspi_selftest.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/spi/xspi_options.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/gpio/xgpio.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/gpio/xgpio_extra.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/gpio/xgpio_g.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/gpio/xgpio_intr.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/gpio/xgpio_selftest.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/gpio/xgpio_sinit.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/common/xbasic_types.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/common/xil_io.c \
	$(FREERTOS_DEMO_DIR)/bsp/xilinx/common/xil_assert.c \
	$(FREERTOS_DEMO_DIR)/devices/serLcd.c \
	$(FREERTOS_DEMO_DIR)/devices/sdmm.c \
	$(FREERTOS_DEMO_DIR)/devices/ff.c \
	$(FREERTOS_DEMO_DIR)/devices/ffsystem.c \
	$(FREERTOS_DEMO_DIR)/devices/ffunicode.c \
	$(FREERTOS_DEMO_DIR)/devices/ds1338rtc.c

ASFLAGS  += -g $(ARCH) $(ABI)  -Wa,-Ilegacy \
	-I$(FREERTOS_SOURCE_DIR)/portable/GCC/RISC-V/chip_specific_extensions/RV32I_CLINT_no_extensions \
	-DportasmHANDLE_INTERRUPT=external_interrupt_handler

FREERTOS_IP_SRC = \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_IP.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_ARP.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_DHCP.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_DNS.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_Sockets.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_TCP_IP.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_UDP_IP.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_TCP_WIN.c \
	$(FREERTOS_TCP_SOURCE_DIR)/FreeRTOS_Stream_Buffer.c \
	$(FREERTOS_TCP_SOURCE_DIR)/portable/BufferManagement/BufferAllocation_2.c \
	$(FREERTOS_TCP_SOURCE_DIR)/portable/NetworkInterface/RISC-V/riscv_hal_eth.c \
	$(FREERTOS_TCP_SOURCE_DIR)/portable/NetworkInterface/RISC-V/NetworkInterface.c \
	$(FREERTOS_DEMO_DIR)/bsp/rand.c

FREERTOS_IP_INCLUDE = \
	-I$(FREERTOS_TCP_SOURCE_DIR) \
	-I$(FREERTOS_TCP_SOURCE_DIR)/include \
	-I$(FREERTOS_TCP_SOURCE_DIR)/portable/Compiler/GCC

FREERTOS_IP_DEMO_SRC = \
	$(FREERTOS_DEMO_DIR)/demo/SimpleUDPClientAndServer.c \
	$(FREERTOS_DEMO_DIR)/demo/TCPEchoClient_SingleTasks.c \
	$(FREERTOS_DEMO_DIR)/demo/SimpleTCPEchoServer.c




INCLUDES += \
	$(FREERTOS_IP_INCLUDE) \
	-I$(FREERTOS_PROTOCOLS_DIR)/include
FREERTOS_SRC += \
	$(FREERTOS_IP_SRC) \
	$(FREERTOS_PROTOCOLS_DIR)/Common/FreeRTOS_TCP_server.c \
	$(FREERTOS_PROTOCOLS_DIR)/HTTP/FreeRTOS_HTTP_server.c \
	$(FREERTOS_PROTOCOLS_DIR)/HTTP/FreeRTOS_HTTP_commands.c \
	$(FREERTOS_PROTOCOLS_DIR)/HTTP/peekpoke.c
# 	DEMO_SRC += $(FREERTOS_IP_DEMO_SRC)

# ifeq ($(PROG),main_blinky)
# 	CFLAGS += -DmainDEMO_TYPE=1
# else 
# ifeq ($(PROG),main_full)
# 	CFLAGS += -DmainDEMO_TYPE=2
# 	PORT_ASM += $(FREERTOS_DEMO_DIR)/demo/RegTest.S
# 	APP_SRC +=  \
# 		$(APP_SOURCE_DIR)/AbortDelay.c \
# 		$(APP_SOURCE_DIR)/BlockQ.c \
# 		$(APP_SOURCE_DIR)/blocktim.c \
# 		$(APP_SOURCE_DIR)/countsem.c \
# 		$(APP_SOURCE_DIR)/death.c \
# 		$(APP_SOURCE_DIR)/dynamic.c \
# 		$(APP_SOURCE_DIR)/integer.c \
# 		$(APP_SOURCE_DIR)/MessageBufferDemo.c \
# 		$(APP_SOURCE_DIR)/PollQ.c \
# 		$(APP_SOURCE_DIR)/GenQTest.c \
# 		$(APP_SOURCE_DIR)/QPeek.c \
# 		$(APP_SOURCE_DIR)/recmutex.c \
# 		$(APP_SOURCE_DIR)/TimerDemo.c \
# 		$(APP_SOURCE_DIR)/EventGroupsDemo.c \
# 		$(APP_SOURCE_DIR)/TaskNotify.c \
# 		$(APP_SOURCE_DIR)/StreamBufferDemo.c \
# 		$(APP_SOURCE_DIR)/StreamBufferInterrupt.c \
# 		$(APP_SOURCE_DIR)/semtest.c
# else
# ifeq ($(PROG),main_iic)
# 	CFLAGS += -DmainDEMO_TYPE=3
# 	INCLUDES += -I$(FREERTOS_DEMO_DIR)/devices
# else
# ifeq ($(PROG),main_gpio)
# 	CFLAGS += -DmainDEMO_TYPE=4
# 	INCLUDES += -I$(FREERTOS_DEMO_DIR)/demo
# else
# ifeq ($(PROG),main_tcp)
# 	CFLAGS += -DmainDEMO_TYPE=5
# 	CFLAGS += -DmainCREATE_TCP_ECHO_SERVER_TASK=1
# 	INCLUDES += $(FREERTOS_IP_INCLUDE)
# 	FREERTOS_SRC += $(FREERTOS_IP_SRC)
# 	DEMO_SRC += $(FREERTOS_IP_DEMO_SRC)
		
# else
# ifeq ($(PROG),main_peekpoke)
# 	CFLAGS += -DmainDEMO_TYPE=9
# 	CFLAGS += -DmainCREATE_PEEKPOKE_SERVER_TASK=1
# 	CFLAGS += -DmainCREATE_HTTP_SERVER=1
# 	CFLAGS += -DipconfigUSE_HTTP=1
# 	CFLAGS += '-DconfigHTTP_ROOT="/notused"'
# 	CFLAGS += -DffconfigMAX_FILENAME=4096
# 	INCLUDES += \
# 		$(FREERTOS_IP_INCLUDE) \
# 		-I$(FREERTOS_PROTOCOLS_DIR)/include
# 	FREERTOS_SRC += \
# 		$(FREERTOS_IP_SRC) \
# 		$(FREERTOS_PROTOCOLS_DIR)/Common/FreeRTOS_TCP_server.c \
# 		$(FREERTOS_PROTOCOLS_DIR)/HTTP/FreeRTOS_HTTP_server.c \
# 		$(FREERTOS_PROTOCOLS_DIR)/HTTP/FreeRTOS_HTTP_commands.c \
# 		$(FREERTOS_PROTOCOLS_DIR)/HTTP/peekpoke.c
# 	DEMO_SRC += $(FREERTOS_IP_DEMO_SRC)
# else
# ifeq ($(PROG),main_udp)
# 	CFLAGS += -DmainDEMO_TYPE=5
# 	CFLAGS += -DmainCREATE_SIMPLE_UDP_CLIENT_SERVER_TASKS=1
# 	INCLUDES += $(FREERTOS_IP_INCLUDE)
# 	FREERTOS_SRC += $(FREERTOS_IP_SRC)
# 	DEMO_SRC += $(FREERTOS_IP_DEMO_SRC)
# else
# ifeq ($(PROG),main_sd)
# 	CFLAGS += -DmainDEMO_TYPE=6
# 	DEMO_SRC += $(FREERTOS_DEMO_DIR)/devices/sdmm.c
# 	DEMO_SRC += $(FREERTOS_DEMO_DIR)/devices/ff.c
# 	DEMO_SRC += $(FREERTOS_DEMO_DIR)/devices/ffsystem.c
# 	DEMO_SRC += $(FREERTOS_DEMO_DIR)/devices/ffunicode.c
# 	INCLUDES += -I$(FREERTOS_DEMO_DIR)/devices
# else
# ifeq ($(PROG),main_uart)
# 	CFLAGS += -DmainDEMO_TYPE=7
# 	INCLUDES += -I$(FREERTOS_DEMO_DIR)/devices
# else
# $(error unknown demo: $(PROG))
# endif
# endif
# endif
# endif
# endif
# endif
# endif
# endif
# endif

ARFLAGS=crsv

#
# Define all object files.
#
RTOS_OBJ = $(FREERTOS_SRC:.c=.o)
APP_OBJ  = $(APP_SRC:.c=.o)
PORT_OBJ = $(PORT_SRC:.c=.o)
DEMO_OBJ = $(DEMO_SRC:.c=.o)
PORT_ASM_OBJ = $(PORT_ASM:.S=.o)
CRT0_OBJ = $(CRT0:.S=.o)
OBJS = $(CRT0_OBJ) $(PORT_ASM_OBJ) $(PORT_OBJ) $(RTOS_OBJ) $(DEMO_OBJ) $(APP_OBJ)

LDFLAGS	 = -T $(FREERTOS_DEMO_DIR)/link.ld -nostartfiles -nostdlib -defsym=_STACK_SIZE=4K
LIBS	 =  -lc -lgcc

$(info ASFLAGS=$(ASFLAGS))
$(info LDLIBS=$(LDLIBS))
$(info CFLAGS=$(CFLAGS))
$(info LDFLAGS=$(LDFLAGS))
$(info ARFLAGS=$(ARFLAGS))

%.o: %.c
	@echo "    CC $<"
	@$(GCC) -c $(CFLAGS) -o $@ $<

%.o: %.S
	@echo "    CC $<"
	@$(GCC) $(ASFLAGS) -c $(CFLAGS) -o $@ $<

all: $(PROG).elf

$(PROG).elf  : $(OBJS) Makefile 
	@echo Linking....
	@$(GCC) -o $@ $(LDFLAGS) $(OBJS) $(LIBS)
	@$(OBJDUMP) -S $(PROG).elf > $(PROG).asm	
	@echo Completed $@

clean :
	@rm -f $(OBJS)
	@rm -f $(PROG).elf 
	@rm -f $(PROG).map
	@rm -f $(PROG).asm

docs :
	@doxygen
