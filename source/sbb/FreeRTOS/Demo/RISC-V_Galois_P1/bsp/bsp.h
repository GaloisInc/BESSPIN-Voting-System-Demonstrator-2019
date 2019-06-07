/*****************************************************************************/
/**
*
* @file bsp.h
* @addtogroup bsp
* @{
*
* Test
* ## This is markdown example
*
* **More** markdown
*
* @note
*
* Lorem impsum
*
*
******************************************************************************/
#ifndef RISCV_P1_BSP_H
#define RISCV_P1_BSP_H

#include "stdint.h"
#include "plic_driver.h"

/**
 * PLIC defines
 */
#define PLIC_BASE_ADDR (0xC000000ULL)

#define PLIC_NUM_SOURCES 16
#define PLIC_NUM_PRIORITIES 16

#define PLIC_SOURCE_UART0 0x1
#define PLIC_SOURCE_ETH 0x2
#define PLIC_SOURCE_DMA_MM2S 0x3
#define PLIC_SOURCE_DMA_S2MM 0x4

#define PLIC_SOURCE_SPI0 0x5
#define PLIC_SOURCE_UART1 0x6
#define PLIC_SOURCE_IIC0 0x7
#define PLIC_SOURCE_SPI1 0x8

#define PLIC_PRIORITY_UART0 0x1
#define PLIC_PRIORITY_ETH 0x2
#define PLIC_PRIORITY_DMA_MM2S 0x3
#define PLIC_PRIORITY_DMA_S2MM 0x3

#define PLIC_PRIORITY_SPI0 0x3
#define PLIC_PRIORITY_UART1 0x1
#define PLIC_PRIORITY_IIC0 0x3
#define PLIC_PRIORITY_SPI1 0x2

extern plic_instance_t Plic;

void prvSetupHardware(void);
void external_interrupt_handler(uint32_t cause);

/**
 * UART defines
 */
#define XPAR_UART_USE_POLLING_MODE 1
#define XPAR_XUARTNS550_NUM_INSTANCES 3
#define XPAR_DEFAULT_BAUD_RATE 115200

#define BSP_USE_UART0 1
#define XPAR_UARTNS550_0_DEVICE_ID 0
#define XPAR_UARTNS550_0_BAUD_RATE XPAR_DEFAULT_BAUD_RATE
#define XPAR_UARTNS550_0_BASEADDR 0x62300000ULL
#define XPAR_UARTNS550_0_CLOCK_HZ configPERIPH_CLOCK_HZ

#define BSP_USE_UART1 1
#define XPAR_UARTNS550_1_DEVICE_ID 1
#define XPAR_UARTNS550_1_BAUD_RATE XPAR_DEFAULT_BAUD_RATE
#define XPAR_UARTNS550_1_BASEADDR (0x62340000ULL)
#define XPAR_UARTNS550_1_CLOCK_HZ configPERIPH_CLOCK_HZ

#define BSP_USE_UART2 1
#define XPAR_UARTNS550_2_DEVICE_ID 2
#define XPAR_UARTNS550_2_BAUD_RATE XPAR_DEFAULT_BAUD_RATE
#define XPAR_UARTNS550_2_BASEADDR (0x62360000ULL)
#define XPAR_UARTNS550_2_CLOCK_HZ configPERIPH_CLOCK_HZ

/**
 * DMA defines
 */
#define BSP_USE_DMA 1
#define XPAR_XAXIDMA_NUM_INSTANCES 1
#define XPAR_AXI_DMA 1

#define XPAR_AXIDMA_0_DEVICE_ID 0
// Virtual base address of DMA engine
#define XPAR_AXIDMA_0_BASEADDR 0x62200000ULL
// Control/status stream
#define XPAR_AXIDMA_0_SG_INCLUDE_STSCNTRL_STRM 1
// AXI4 memory-mapped to stream
#define XPAR_AXIDMA_0_INCLUDE_MM2S 1
// Allow unaligned transfers
#define XPAR_AXIDMA_0_INCLUDE_MM2S_DRE 1
#define XPAR_AXIDMA_0_M_AXI_MM2S_DATA_WIDTH 32
// AXI stream to memory-mapped TODO: Rx?
#define XPAR_AXIDMA_0_INCLUDE_S2MM 1
// Allow unaligned transfers
#define XPAR_AXIDMA_0_INCLUDE_S2MM_DRE 1
#define XPAR_AXIDMA_0_M_AXI_S2MM_DATA_WIDTH 32
// Scatter-gather engine
#define XPAR_AXIDMA_0_INCLUDE_SG 1
#define XPAR_AXIDMA_0_NUM_MM2S_CHANNELS 1
#define XPAR_AXIDMA_0_NUM_S2MM_CHANNELS 1
#define XPAR_AXI_DMA_0_MM2S_BURST_SIZE 16
#define XPAR_AXI_DMA_0_S2MM_BURST_SIZE 16
#define XPAR_AXI_DMA_0_MICRO_DMA 0
#define XPAR_AXI_DMA_0_ADDR_WIDTH 64
#define XPAR_AXIDMA_0_SG_LENGTH_WIDTH 16

/**
 * Ethernet defines
 */
#define BSP_USE_ETHERNET 1
#define XPAR_XAXIETHERNET_NUM_INSTANCES 1

#define XPAR_AXIETHERNET_0_PHYADDR 0x03
#define XPAR_AXIETHERNET_0_DEVICE_ID 0
#define XPAR_AXIETHERNET_0_BASEADDR 0x62100000ULL
// 0 for SoftTemac at 10/100 Mbps, 1 for SoftTemac at 10/100/1000 Mbps and 2 for Vitex6 Hard Temac
#define XPAR_AXIETHERNET_0_TEMAC_TYPE 2 // TODO: not sure if this is right
// TxCsum indicates that the device has checksum offload on the Tx channel or not.
#define XPAR_AXIETHERNET_0_TXCSUM 0
// RxCsum indicates that the device has checksum offload on the Rx channel or not.
#define XPAR_AXIETHERNET_0_RXCSUM 0
// PhyType indicates which type of PHY interface is used (MII, GMII, RGMII, etc.)
#define XPAR_AXIETHERNET_0_PHY_TYPE XAE_PHY_TYPE_SGMII
#define XPAR_AXIETHERNET_0_TXVLAN_TRAN 0
#define XPAR_AXIETHERNET_0_RXVLAN_TRAN 0
#define XPAR_AXIETHERNET_0_TXVLAN_TAG 0
#define XPAR_AXIETHERNET_0_RXVLAN_TAG 0
#define XPAR_AXIETHERNET_0_TXVLAN_STRP 0
#define XPAR_AXIETHERNET_0_RXVLAN_STRP 0
// Extended multicast address filtering
#define XPAR_AXIETHERNET_0_MCAST_EXTEND 0
// Statistics gathering options
#define XPAR_AXIETHERNET_0_STATS 1
// Ethernet Audio Video Bridging
#define XPAR_AXIETHERNET_0_AVB 0
// SGMII over LVDS
#define XPAR_AXIETHERNET_0_ENABLE_SGMII_OVER_LVDS 1
// Enable 1588 option.
#define XPAR_AXIETHERNET_0_ENABLE_1588 0
// Tells whether MAC is 1G or 2p5G.
#define XPAR_AXIETHERNET_0_SPEED XAE_SPEED_1000_MBPS // TODO: not sure if this is right
// Number of table entries for the multicast address filtering // TODO: we are not using it
#define XPAR_AXIETHERNET_0_NUM_TABLE_ENTRIES 4
// Axi Ethernet interrupt ID.
#define XPAR_AXIETHERNET_0_INTR PLIC_SOURCE_ETH // TODO: doesn't appear to be used
// AxiDevType is the type of device attached to the Axi Ethernet's AXI4-Stream interface.
#define XPAR_AXIETHERNET_0_CONNECTED_TYPE XPAR_AXI_DMA
// AxiDevBaseAddress is the base address of the device attached to the Axi Ethernet's AXI4-Stream interface.
#define XPAR_AXIETHERNET_0_CONNECTED_BASEADDR 0x62200000ULL // DMA base address
// Unused
#define XPAR_AXIETHERNET_0_FIFO_INTR 0xFF
// Axi DMA RX interrupt ID
#define XPAR_AXIETHERNET_0_DMA_RX_INTR PLIC_SOURCE_DMA_S2MM
// Axi DMA TX interrupt ID
#define XPAR_AXIETHERNET_0_DMA_TX_INTR PLIC_SOURCE_DMA_MM2S

/**
 * IIC Defines
 */
#define XPAR_XIIC_NUM_INSTANCES 1

#define BSP_USE_IIC0 1
#define XPAR_IIC_0_DEVICE_ID 0
#define XPAR_IIC_0_BASEADDR (0x62310000ULL)
#define XPAR_IIC_0_TEN_BIT_ADR 0
#define XPAR_IIC_0_GPO_WIDTH 32

/**
 * SPI defines
 */
#define XPAR_XSPI_NUM_INSTANCES 2
#define XPAR_SPI_USE_POLLING_MODE 1

#define BSP_USE_SPI0 0 /* SPI0 is Flash memory, don't use it directly */
#define XPAR_SPI_0_DEVICE_ID 0
#define XPAR_SPI_0_BASEADDR 0x4000000ULL
#define XPAR_SPI_0_FIFO_EXIST 0
#define XPAR_SPI_0_SLAVE_ONLY 0
#define XPAR_SPI_0_NUM_SS_BITS 0
#define XPAR_SPI_0_NUM_TRANSFER_BITS 0
#define XPAR_SPI_0_SPI_MODE 0
#define XPAR_SPI_0_AXI_INTERFACE 0
#define XPAR_SPI_0_AXI_FULL_BASEADDR 0
#define XPAR_SPI_0_XIP_MODE 0
#define XPAR_SPI_0_USE_STARTUP 0

#define BSP_USE_SPI1 1 /* SPI1 is used for SD card (polled mode), and can be used for LCD screen (interrupt mode)*/ 
#define XPAR_SPI_1_DEVICE_ID 1
#define XPAR_SPI_1_BASEADDR (0x62320000ULL)
#define XPAR_SPI_1_FIFO_EXIST 0
#define XPAR_SPI_1_SLAVE_ONLY 0
#define XPAR_SPI_1_NUM_SS_BITS 1
#define XPAR_SPI_1_NUM_TRANSFER_BITS 8
#define XPAR_SPI_1_SPI_MODE 0
#define XPAR_SPI_1_AXI_INTERFACE 0
#define XPAR_SPI_1_AXI_FULL_BASEADDR 0
#define XPAR_SPI_1_XIP_MODE 0
#define XPAR_SPI_1_USE_STARTUP 0

/**
 * GPIO defines
 */
#define BSP_USE_GPIO 1
#define XPAR_XGPIO_NUM_INSTANCES 1
#define XPAR_GPIO_0_DEVICE_ID 0
#define XPAR_GPIO_0_BASEADDR 0x62330000ULL
#define XPAR_GPIO_0_INTERRUPT_PRESENT 0
#define XPAR_GPIO_0_IS_DUAL 1

/**
 * Xilinx Drivers defines
 * Some xillinx drivers require to sleep for given number of seconds
 */
#include "FreeRTOS.h"
#include "task.h"

#define sleep(_SECS) vTaskDelay(pdMS_TO_TICKS(_SECS * 1000));
#define msleep(_MSECS) vTaskDelay(pdMS_TO_TICKS(_MSECS));

#endif /* RISCV_P1_BSP_H */
