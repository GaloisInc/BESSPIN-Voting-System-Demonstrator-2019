#ifndef __SPI_H__
#define __SPI_H__

#include "bsp.h"
#include "xspi.h"
#include "semphr.h"


    /* Device driver for SPI peripheral */
    struct SpiDriver
    {
        XSpi Device; /* Xilinx SPI driver */
        /* Counters used to determine when buffer has been send and received */
        volatile int TotalTransactiondCount;
        volatile int TotalErrorCount;
        volatile int Errors;
        SemaphoreHandle_t mutex;  /* Mutex for bus acquisition */
        volatile TaskHandle_t task_handle; /* handle for task that initiated a transaction */
    };

#if BSP_USE_SPI0
    extern struct SpiDriver Spi0;
    void spi0_init(void);
    int spi0_transmit(uint8_t slave_id, uint8_t* tx_buf, uint8_t len);
    int spi0_receive(uint8_t slave_id, uint8_t* rx_buf, uint8_t len);
    int spi0_transceive(uint8_t slave_id, uint8_t* tx_buf, uint8_t* rx_buf, uint8_t len);
#endif

#if BSP_USE_SPI1
    extern struct SpiDriver Spi1;
    void spi1_init(void);
    int spi1_transmit(uint8_t slave_id, uint8_t* tx_buf, uint8_t len);
    int spi1_receive(uint8_t slave_id, uint8_t* rx_buf, uint8_t len);
    int spi1_transceive(uint8_t slave_id, uint8_t* tx_buf, uint8_t* rx_buf, uint8_t len);
#endif

#endif
