#include "spi.h"
#include "xspi.h"
#include "semphr.h"
#include <stdio.h>

/*****************************************************************************/
/* Structs */

/*****************************************************************************/
/* Static functions, macros etc */
static void spi_init(struct SpiDriver *Spi, uint8_t device_id, uint8_t plic_source_id);
static int spi_transfer(struct SpiDriver *Spi, uint8_t slave_id, uint8_t *tx_buf, uint8_t *rx_buf, uint8_t len);
static void SpiStatusHandler(void *CallBackRef, int StatusEvent, int ByteCount);

/*****************************************************************************/
/* Global defines */

#define SPI_TRANSACTION_DELAY_MS 500

/* Instance of SPI device */
#if BSP_USE_SPI0
XSpi XSpi0;
struct SpiDriver Spi0;

/**
 * Initialize SPI0
 */
void spi0_init(void)
{
    spi_init(&Spi0, XPAR_SPI_0_DEVICE_ID, PLIC_SOURCE_SPI0);
}

/**
 * Transmit data to `slave_id` at SPI0
 */
int spi0_transmit(uint8_t slave_id, uint8_t *tx_buf, uint8_t len)
{
    return spi_transfer(&Spi0, slave_id, tx_buf, NULL, len);
}

/**
 * Receive data from `slave_id` at SPI0
 */
int spi0_receive(uint8_t slave_id, uint8_t *rx_buf, uint8_t len)
{
    return spi_transfer(&Spi0, slave_id, rx_buf, rx_buf, len);
}

/**
 * Transmit and receive `len` data from `slave_id` at SPI0
 * NOTE: tx_len = rx_len
 */
int spi0_transceive(uint8_t slave_id, uint8_t *tx_buf, uint8_t *rx_buf, uint8_t len)
{
    return spi_transfer(&Spi0, slave_id, rx_buf, tx_buf, len);
}
#endif /* BSP_USE_SPI0 */


/* Instance of SPI device */
#if BSP_USE_SPI1
XSpi XSpi1;
struct SpiDriver Spi1;

/**
 * Initialize SPI1
 */
void spi1_init(void)
{
    spi_init(&Spi1, XPAR_SPI_1_DEVICE_ID, PLIC_SOURCE_SPI1);
}

/**
 * Transmit data to `slave_id` at SPI1
 */
int spi1_transmit(uint8_t slave_id, uint8_t *tx_buf, uint8_t len)
{
    return spi_transfer(&Spi1, slave_id, tx_buf, NULL, len);
}

/**
 * Receive data from `slave_id` at SPI1
 */
int spi1_receive(uint8_t slave_id, uint8_t *rx_buf, uint8_t len)
{
    return spi_transfer(&Spi1, slave_id, rx_buf, rx_buf, len);
}

/**
 * Transmit and receive `len` data from `slave_id` at SPI1
 * NOTE: tx_len = rx_len
 */
int spi1_transceive(uint8_t slave_id, uint8_t *tx_buf, uint8_t *rx_buf, uint8_t len)
{
    return spi_transfer(&Spi1, slave_id, rx_buf, tx_buf, len);
}
#endif /* BSP_USE_SPI1 */

/*****************************************************************************/

__attribute__((unused)) static void spi_init(struct SpiDriver *Spi, uint8_t device_id, uint8_t plic_source_id)
{
    // Initialize struct
    Spi->mutex = xSemaphoreCreateMutex();
    switch (device_id)
    {
#if BSP_USE_SPI0
    case 0:
        Spi->Device = XSpi0;
        break;
#endif
#if BSP_USE_SPI1
    case 1:
        Spi->Device = XSpi1;
        break;
#endif
    default:
        // Trigger a fault: unsupported device ID
        configASSERT(0);
        break;
    };

    Spi->task_handle = NULL;
    Spi->TotalTransactiondCount = 0;
    Spi->TotalErrorCount = 0;
    Spi->Errors = 0;

    /* Initialize the XIic driver so that it's ready to use */
    configASSERT(XSpi_Initialize(&Spi->Device, device_id) == XST_SUCCESS);

    /* Perform a self-test to ensure that the hardware was built correctly */
    configASSERT(XSpi_SelfTest(&Spi->Device) == XST_SUCCESS);

#if !XPAR_SPI_USE_POLLING_MODE /* Interrup mode */
    /* Setup SPI status handler to indicate that SpiStatusHandler
    should be called when there is an interrupt */
    XSpi_SetStatusHandler(&Spi->Device, Spi,
                          (XSpi_StatusHandler)SpiStatusHandler);

    /* Setup interrupt system */
    configASSERT(PLIC_register_interrupt_handler(&Plic, plic_source_id,
                                                 (XInterruptHandler)XSpi_InterruptHandler, &Spi->Device) != 0);
#endif /* XPAR_SPI_USE_POLLING_MODE */
    
    /* Set device to master mode */
    configASSERT(XSpi_SetOptions(&Spi->Device, XSP_MASTER_OPTION | XSP_MANUAL_SSELECT_OPTION) == XST_SUCCESS);

    /* Start the SPI driver so that the device and interrupts are enabled */
    XSpi_Start(&Spi->Device);

#if XPAR_SPI_USE_POLLING_MODE
    /*
	 * Disable Global interrupt to use polled mode operation
	 */
	XSpi_IntrGlobalDisable(&Spi->Device);

    (void) plic_source_id;
    (void) SpiStatusHandler;
#endif
}

__attribute__((unused)) static int spi_transfer(struct SpiDriver *Spi, uint8_t slave_id, uint8_t *tx_buf, uint8_t *rx_buf, uint8_t len)
{
    int returnval;
    configASSERT(Spi->mutex != NULL);
    configASSERT(xSemaphoreTake(Spi->mutex, portMAX_DELAY) == pdTRUE);

    /* Select the slave*/
    configASSERT(XSpi_SetSlaveSelect(&Spi->Device, slave_id) == XST_SUCCESS);

    /* Get task handle */
    Spi->task_handle = xTaskGetCurrentTaskHandle();

    // TODO: handle BUSY and other states
    //int val = XSpi_Transfer(&Spi->Device, tx_buf, rx_buf, len);
    //printf("spi val: %i\r\n", val);

    /* Initialize transfer */
    configASSERT(XSpi_Transfer(&Spi->Device, tx_buf, rx_buf, len) == XST_SUCCESS);

    /* wait for notification */
    if (xTaskNotifyWait(0, 0, NULL, pdMS_TO_TICKS(SPI_TRANSACTION_DELAY_MS)))
    {
        /* Check Error value */
        if (Spi->Errors != 0)
        {
            // an error occured
            returnval = -1;
        }
        else
        {
            /* Transaction succesfull, return number of transmitted bytes */
            returnval = Spi->TotalTransactiondCount;
        }
    }
    else
    {
        /* timeout occured */
        returnval = -1;
    }

    /* Deselect slave */
    configASSERT(XSpi_SetSlaveSelect(&Spi->Device, 0) == XST_SUCCESS);

    /* Release mutex and return */
    xSemaphoreGive(Spi->mutex);
    return returnval;
}

/*****************************************************************************/
/**
*
* This function is the handler which performs processing for the SPI driver.
* It is called from an interrupt context such that the amount of processing
* performed should be minimized. It is called when a transfer of SPI data
* completes or an error occurs.
*
* This handler provides an example of how to handle SPI interrupts and
* is application specific.
*
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
* @param	StatusEvent is the event that just occurred.
* @param	ByteCount is the number of bytes transferred up until the event
*		occurred.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void SpiStatusHandler(void *CallBackRef, int StatusEvent, int ByteCount)
{
    struct SpiDriver *Spi = (struct SpiDriver *)CallBackRef;

    /* If event was not transfer done, track it as an error */
    if (StatusEvent != XST_SPI_TRANSFER_DONE)
    {
        Spi->Errors = StatusEvent;
        Spi->TotalErrorCount++;
    }
    else
    {
        /* All OK */
        Spi->TotalTransactiondCount = ByteCount;
        Spi->Errors = 0;
    }

    configASSERT(Spi->task_handle != NULL);
    static BaseType_t askForContextSwitch = pdFALSE;
    vTaskNotifyGiveFromISR(Spi->task_handle, &askForContextSwitch);
}