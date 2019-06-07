#include "iic.h"
#include "xiic.h"
#include "semphr.h"
#include <stdio.h>

/*****************************************************************************/
/* Structs */

/*****************************************************************************/
/* Static functions, macros etc */

static void iic_init(struct IicDriver *Iic, uint8_t device_id, uint8_t plic_source_id);
int iic_transmit(struct IicDriver *Iic, uint8_t addr, uint8_t *tx_data, uint8_t tx_len);
int iic_receive(struct IicDriver *Iic, uint8_t addr, uint8_t *rx_data, uint8_t rx_len);

static void RecvHandler(void *CallbackRef, int ByteCount);
static void SendHandler(void *CallbackRef, int Status);
static void StatusHandler(void *CallbackRef, int Status);

/*****************************************************************************/
/* Global defines */

#define IIC_TRANSACTION_DELAY_MS 500

/* Instance of IIC devices */
#if BSP_USE_IIC0
XIic XIic0;
struct IicDriver Iic0;
#endif

#if BSP_USE_IIC1
XIic XIic1;
struct IicDriver Iic1;
#endif

/*****************************************************************************/

/**
 * Initialize IIC peripheral. 
 */
__attribute__((unused)) static void iic_init(struct IicDriver *Iic, uint8_t device_id, uint8_t plic_source_id)
{
    // Initialize struct
    Iic->mutex = xSemaphoreCreateMutex();
    switch (device_id)
    {
#if BSP_USE_IIC0
    case 0:
        Iic->Device = XIic0;
        break;
#endif
#if BSP_USE_IIC1
    case 1:
        Iic->Device = XIic1;
        break;
#endif
    default:
        // Trigger a fault: unsupported device ID
        configASSERT(0);
        break;
    };

    Iic->task_handle = NULL;
    Iic->TotalErrorCount = 0;
    Iic->Errors = 0;

    /* Initialize the XIic driver so that it's ready to use */
    configASSERT(XIic_Initialize(&Iic->Device, device_id) == XST_SUCCESS);

    /* Perform a self-test to ensure that the hardware was built correctly */
    configASSERT(XIic_SelfTest(&Iic->Device) == XST_SUCCESS);

    /*
	 * Setup handler to process the asynchronous events which occur,
	 * the driver is only interrupt driven such that this must be
	 * done prior to starting the device.
	 */
    XIic_SetRecvHandler(&Iic->Device, Iic, RecvHandler);
    XIic_SetSendHandler(&Iic->Device, Iic, SendHandler);
    XIic_SetStatusHandler(&Iic->Device, Iic, StatusHandler);

    /* Setup interrupt system */
    configASSERT(PLIC_register_interrupt_handler(&Plic, plic_source_id,
                                                 (XInterruptHandler)XIic_InterruptHandler, &Iic->Device) != 0);

    /*
	 * Start the IIC driver such that it is ready to send and
	 * receive messages on the IIC interface, set the address
	 * to send to which is the temperature sensor address
	 */
    XIic_Start(&Iic->Device);
}

/**
 * Transmit data over IIC bus. Synchronous API, this function blocks until the transaction ends.
 * 
 * @param Iic is the device driver
 * @param addr is the address of the slave device
 * @param tx_data is the data buffer
 * @param tx_len is the length of tx_data (and the number of bytes to be sent)
 */
int iic_transmit(struct IicDriver *Iic, uint8_t addr, uint8_t *tx_data, uint8_t tx_len)
{
    int returnval;
    configASSERT(Iic->mutex != NULL);
    configASSERT(xSemaphoreTake(Iic->mutex, portMAX_DELAY) == pdTRUE);
    configASSERT(XIic_SetAddress(&Iic->Device, XII_ADDR_TO_SEND_TYPE, addr) == XST_SUCCESS);

    Iic->task_handle = xTaskGetCurrentTaskHandle();
    Iic->trans_len = tx_len;

    // TODO: handle XST_IIC_BUS_BUSY (it should never happen, we have only one master)
    configASSERT(XIic_MasterSend(&Iic->Device, tx_data, (int)tx_len) == XST_SUCCESS);

    /* wait for notification */
    if (xTaskNotifyWait(0, 0, NULL, pdMS_TO_TICKS(IIC_TRANSACTION_DELAY_MS)))
    {
        /* Check Error value */
        if (Iic->Errors != 0)
        {
            // an error occured
            configASSERT(Iic->Errors == XII_SLAVE_NO_ACK_EVENT); // TODO: remove?
            printf("Error occured: %i\n", Iic->Errors);
            returnval = -1;
        }
        else
        {
            /* Transaction succesfull, return number of transmitted bytes */
            returnval = Iic->trans_len;
        }
    }
    else
    {
        /* timeout occured */
        returnval = -1;
    }

    /* Release mutex and return */
    xSemaphoreGive(Iic->mutex);
    return returnval;
}

/**
 * Receive data over IIC bus. Synchronous API, this function blocks until the transaction ends.
 * 
 * @param Iic is the device driver
 * @param addr is the address of the slave device
 * @param tx_data is the data buffer
 * @param tx_len is the length of rx_data (and the number of bytes to be received)
 */
int iic_receive(struct IicDriver *Iic, uint8_t addr, uint8_t *rx_data, uint8_t rx_len)
{
    int returnval;
    configASSERT(Iic->mutex != NULL);
    configASSERT(xSemaphoreTake(Iic->mutex, portMAX_DELAY) == pdTRUE);
    configASSERT(XIic_SetAddress(&Iic->Device, XII_ADDR_TO_SEND_TYPE, addr) == XST_SUCCESS);

    Iic->task_handle = xTaskGetCurrentTaskHandle();
    Iic->trans_len = rx_len;

    // TODO: handle XST_IIC_BUS_BUSY (it should never happen, we have only one master)
    configASSERT(XIic_MasterRecv(&Iic->Device, rx_data, (int)rx_len) == XST_SUCCESS);

    /* wait for notification */
    if (xTaskNotifyWait(0, 0, NULL, pdMS_TO_TICKS(IIC_TRANSACTION_DELAY_MS)))
    {
        /* Check Error value */
        if (Iic->Errors != 0)
        {
            // an error occured
            configASSERT(Iic->Errors == XII_SLAVE_NO_ACK_EVENT); // TODO: remove?
            printf("Error occured: %i\n", Iic->Errors);
            returnval = -1;
        }
        else
        {
            /* Transaction succesfull, return number of transmitted bytes */
            returnval = Iic->trans_len;
        }
    }
    else
    {
        /* timeout occured */
        returnval = -1;
    }

    /* Release mutex and return */
    xSemaphoreGive(Iic->mutex);
    return returnval;
}

/*****************************************************************************/
/**
* This receive handler is called asynchronously from an interrupt context and
* and indicates that data in the specified buffer was received. The byte count
* should equal the byte count of the buffer if all the buffer was filled.
*
* @param	CallBackRef is a pointer to the IIC device driver instance which
*		the handler is being called for.
* @param	ByteCount indicates the number of bytes remaining to be received of
*		the requested byte count. A value of zero indicates all requested
*		bytes were received.
*
* @return	None.
*
* @notes	None.
*
****************************************************************************/
static void RecvHandler(void *CallbackRef, int ByteCount)
{
    struct IicDriver *Iic = (struct IicDriver *)CallbackRef;

    if (ByteCount != 0)
    {
        // do nothing untill we receive all the bytes
        return;
    }

    configASSERT(Iic->task_handle != NULL);
    static BaseType_t askForContextSwitch = pdFALSE;
    vTaskNotifyGiveFromISR(Iic->task_handle, &askForContextSwitch);
}

/****************************************************************************/
/**
* This Send handler is called asynchronously from an interrupt
* context and indicates that data in the specified buffer has been sent.
*
* @param	InstancePtr is a pointer to the IIC driver instance for which
*		the handler is being called for.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
static void SendHandler(void *CallbackRef, int Status)
{
    struct IicDriver *Iic = (struct IicDriver *)CallbackRef;
    // TODO: not much to do here?
    configASSERT(Status == 0);

    // Notify the task
    configASSERT(Iic->task_handle != NULL);
    static BaseType_t askForContextSwitch = pdFALSE;
    vTaskNotifyGiveFromISR(Iic->task_handle, &askForContextSwitch);
}

/*****************************************************************************/
/**
* This status handler is called asynchronously from an interrupt context and
* indicates that the conditions of the IIC bus changed. This  handler should
* not be called for the application unless an error occurs.
*
* @param	CallBackRef is a pointer to the IIC device driver instance which the
*		handler is being called for.
* @param	Status contains the status of the IIC bus which changed.
*
* @return	None.
*
* @notes	None.
*
****************************************************************************/
static void StatusHandler(void *CallbackRef, int Status)
{
    struct IicDriver *Iic = (struct IicDriver *)CallbackRef;
    Iic->TotalErrorCount++;
    Iic->Errors = Status;

    // An error occured, notify the task
    configASSERT(Iic->task_handle != NULL);
    static BaseType_t askForContextSwitch = pdFALSE;
    vTaskNotifyGiveFromISR(Iic->task_handle, &askForContextSwitch);
}

#if BSP_USE_IIC0
void iic0_init(void)
{
    iic_init(&Iic0, XPAR_IIC_0_DEVICE_ID, PLIC_SOURCE_IIC0);
}

int iic0_transmit(uint8_t addr, uint8_t *tx_data, uint8_t tx_len)
{
    return iic_transmit(&Iic0, addr, tx_data, tx_len);
}

int iic0_receive(uint8_t addr, uint8_t *rx_data, uint8_t rx_len)
{
    return iic_receive(&Iic0, addr, rx_data, rx_len);
}
#endif

#if BSP_USE_IIC1
void iic1_init(void)
{
    iic_init(&Iic1, XPAR_IIC_1_DEVICE_ID, PLIC_SOURCE_IIC1);
}

int iic1_transmit(uint8_t addr, uint8_t *tx_data, uint8_t tx_len)
{
    return iic_transmit(&Iic1, addr, tx_data, tx_len);
}

int iic1_receive(uint8_t addr, uint8_t *rx_data, uint8_t rx_len)
{
    return iic_receive(&Iic1, addr, rx_data, rx_len);
}
#endif