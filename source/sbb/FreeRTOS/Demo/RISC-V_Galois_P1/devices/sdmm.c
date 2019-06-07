/*------------------------------------------------------------------------/
/  Foolproof MMCv3/SDv1/SDv2 (in SPI mode) control module
/-------------------------------------------------------------------------/
/
/  Copyright (C) 2013, ChaN, all right reserved.
/
/ * This software is a free software and there is NO WARRANTY.
/ * No restriction on use. You can use, modify and redistribute it for
/   personal, non-profit or commercial products UNDER YOUR RESPONSIBILITY.
/ * Redistributions of source code must retain the above copyright notice.
/
/-------------------------------------------------------------------------*/

#include "diskio.h" /* Common include file for FatFs and disk I/O layer */

/*-------------------------------------------------------------------------*/
/* Platform dependent macros and functions needed to be modified           */
/*-------------------------------------------------------------------------*/
#include "xspi.h"
#include "spi.h"
#include <stdio.h>
#include <stdbool.h>
#include "SdInfo.h"
#include <string.h>

#define SDMMC_DEBUG_PRINT 0

/*--------------------------------------------------------------------------

   Module Private Functions

---------------------------------------------------------------------------*/
static bool isTimedOut(uint16_t startMS, uint16_t timeoutMS);
static bool waitNotBusy(uint16_t timeoutMS);
static uint8_t cardCommand(uint8_t cmd, uint32_t arg);
static uint8_t spiReceive(void);
static uint8_t spiReceiveBuf(uint8_t *data, uint16_t len);
static void spiSend(uint8_t data);
static void spiSendBuf(uint8_t *data, uint16_t len);
static uint8_t cardAcmd(uint8_t cmd, uint32_t arg);
static void card_select(void);
static void card_deselect(void);
static bool readStart(uint32_t blockNumber);
static bool readData(uint8_t *dst, size_t count);
static bool readStop(void);
static uint8_t type(void);
static bool readRegister(uint8_t cmd, void *buf);
static bool isBusy(void);
static bool writeStart(uint32_t blockNumber);
static bool writeData(uint8_t *src);
static bool writeDataBuf(uint8_t token, uint8_t *src);
static bool writeStop(void);

static uint8_t m_status = 0;
static uint8_t m_type = 0;
static uint8_t Stat = STA_NOINIT; /* Disk status */

static bool writeStart(uint32_t blockNumber)
{
    // use address if not SDHC card
    if (type() != SD_CARD_TYPE_SDHC)
    {
        blockNumber <<= 9;
    }
    if (cardCommand(CMD25, blockNumber))
    {
        printf("Error: SD_CARD_ERROR_CMD25\r\n");
        return false;
    }
    return true;
}

static bool writeData(uint8_t *src)
{
    // wait for previous write to finish
    if (!waitNotBusy(SD_WRITE_TIMEOUT))
    {
        printf("Error: SD_CARD_ERROR_WRITE_TIMEOUT\r\n");
        return false;
    }

    if (!writeDataBuf((uint8_t)WRITE_MULTIPLE_TOKEN, src))
    {
        printf("Error: writeData(WRITE_MULTIPLE_TOKEN, src)\r\n");
        return false;
    }
    return true;
}

// send one block of data for write block or write multiple blocks
static bool writeDataBuf(uint8_t token, uint8_t *src)
{
    uint16_t crc = 0XFFFF;
    spiSend(token);
    spiSendBuf(src, 512);
    spiSend(crc >> 8);
    spiSend(crc & 0XFF);

    m_status = spiReceive();
    if ((m_status & DATA_RES_MASK) != DATA_RES_ACCEPTED)
    {
        printf("Error: SD_CARD_ERROR_WRITE\r\n");
        return false;
    }
    return true;
}

static bool writeStop(void)
{
    if (!waitNotBusy(SD_WRITE_TIMEOUT))
    {
        printf("Error: SD_CARD_ERROR_STOP_TRAN\r\n");
        return false;
    }
    spiSend(STOP_TRAN_TOKEN);
    return true;
}

static bool isBusy(void)
{
    bool rtn = true;
    for (uint8_t i = 0; i < 8; i++)
    {
        if (0XFF == spiReceive())
        {
            rtn = false;
            break;
        }
    }
    return rtn;
}

/** Return the card type: SD V1, SD V2 or SDHC
   * \return 0 - SD V1, 1 - SD V2, or 3 - SDHC.
   */
static uint8_t type(void)
{
    return m_type;
}

/** read CID or CSR register */
static bool readRegister(uint8_t cmd, void *buf)
{
    uint8_t *dst = (uint8_t *)(buf);

    card_select();
    if (cardCommand(cmd, 0))
    {
        printf("Error: SD_CARD_ERROR_READ_REG\r\n");
        return false;
    }
    if (!readData(dst, 16))
    {
        printf("Error: readData(dst, 16)\r\n");
        return false;
    }
    return true;
}

/*-----------------------------------------------------------------------*/
/* Receive a single byte from the card	                                 */
/*-----------------------------------------------------------------------*/
static uint8_t spiReceive(void)
{
    uint8_t rx = 0xFF;
    configASSERT(XSpi_Transfer(&Spi1.Device, &rx, &rx, 1) == 0);
    return rx;
}

/*-----------------------------------------------------------------------*/
/* Receive a buffer from the card	                                 */
/*-----------------------------------------------------------------------*/
static uint8_t spiReceiveBuf(uint8_t *data, uint16_t len)
{
    configASSERT(len > 0);
    configASSERT(XSpi_Transfer(&Spi1.Device, data, data, len) == 0);
    return 0;
}

/*-----------------------------------------------------------------------*/
/* Transmit a single byte to the card	                                 */
/*-----------------------------------------------------------------------*/
static void spiSend(uint8_t data)
{
    configASSERT(XSpi_Transfer(&Spi1.Device, &data, NULL, 1) == 0);
}

/*-----------------------------------------------------------------------*/
/* Transmit a buffer to the card		                                 */
/*-----------------------------------------------------------------------*/
static void spiSendBuf(uint8_t *data, uint16_t len)
{
    configASSERT(XSpi_Transfer(&Spi1.Device, data, NULL, len) == 0);
}

/*-----------------------------------------------------------------------*/
/* Check if a timeout occured			                                 */
/*-----------------------------------------------------------------------*/
static bool isTimedOut(uint16_t startMS, uint16_t timeoutMS)
{
    return (xTaskGetTickCount() - startMS) > timeoutMS;
}

/*-----------------------------------------------------------------------*/
/* Wait for the card to become not busy                                  */
/*-----------------------------------------------------------------------*/
static bool waitNotBusy(uint16_t timeoutMS)
{
    uint16_t t0 = xTaskGetTickCount();
    // Check not busy first since yield is not called in isTimedOut.
    while (spiReceive() != 0XFF)
    {
        if (isTimedOut(t0, timeoutMS))
        {
            return false;
        }
    }
    return true;
}

/*-----------------------------------------------------------------------*/
/* Send a command to the card				                             */
/*-----------------------------------------------------------------------*/
static uint8_t cardCommand(uint8_t cmd, uint32_t arg)
{
    // wait if busy unless CMD0
    if (cmd != CMD0)
    {
        waitNotBusy(SD_CMD_TIMEOUT);
    }

    // form message
    uint8_t buf[6];
    buf[0] = (uint8_t)0x40U | cmd;
    buf[1] = (uint8_t)(arg >> 24U);
    buf[2] = (uint8_t)(arg >> 16U);
    buf[3] = (uint8_t)(arg >> 8U);
    buf[4] = (uint8_t)arg;
    buf[5] = cmd == CMD0 ? 0X95 : 0X87; //TODO: should be a CRC?

    // send message
    spiSendBuf(buf, 6);

    // discard first fill byte to avoid MISO pull-up problem.
    spiReceive();

    // there are 1-8 fill bytes before response.  fill bytes should be 0XFF.
    for (uint8_t i = 0; ((m_status = spiReceive()) & 0X80) && i < 10; i++)
    {
        // intentionally empty body
    }

    return m_status;
}

/*-----------------------------------------------------------------------*/
/* Send ACMD							                                 */
/*-----------------------------------------------------------------------*/
static uint8_t cardAcmd(uint8_t cmd, uint32_t arg)
{
    cardCommand(CMD55, 0);
    return cardCommand(cmd, arg);
}

/*-----------------------------------------------------------------------*/
/* Select slave							                                 */
/*-----------------------------------------------------------------------*/
static void card_select(void)
{
    configASSERT(XSpi_SetSlaveSelect(&Spi1.Device, 1) == 0);
}

/*-----------------------------------------------------------------------*/
/* Deselect slave						                                 */
/*-----------------------------------------------------------------------*/
static void card_deselect(void)
{
    configASSERT(XSpi_SetSlaveSelect(&Spi1.Device, 0) == 0);
}

/*-----------------------------------------------------------------------*/
/* Receive a data packet from the card                                   */
/*-----------------------------------------------------------------------*/
static bool readData(uint8_t *dst, size_t count)
{
    // wait for start block token
    uint16_t t0 = xTaskGetTickCount();
    while ((m_status = spiReceive()) == 0XFF)
    {
        if (isTimedOut(t0, SD_READ_TIMEOUT))
        {
            printf("Error: SD_CARD_ERROR_READ_TIMEOUT\r\n");
            return false;
        }
    }
    if (m_status != DATA_START_BLOCK)
    {
        printf("Error: SD_CARD_ERROR_READ\r\n");
        return false;
    }
    // transfer data
    if ((m_status = spiReceiveBuf(dst, count)))
    {
        printf("Error: SD_CARD_ERROR_DMA\r\n");
        return false;
    }

    // discard crc
    spiReceive();
    spiReceive();
    return true;
}

static bool readStart(uint32_t blockNumber)
{
    #if SDMMC_DEBUG_PRINT
        printf("Read Start: %lu\r\n", blockNumber);
    #endif
    if (type() != SD_CARD_TYPE_SDHC)
    {
        blockNumber <<= 9;
    }
    if (cardCommand(CMD18, blockNumber))
    {
        printf("Error: SD_CARD_ERROR_CMD18\r\n");
        return false;
    }
    return true;
}

static bool readStop(void)
{
    if (cardCommand(CMD12, 0))
    {
        printf("Error: SD_CARD_ERROR_CMD12\r\n");
        return false;
    }
    return true;
}
/*--------------------------------------------------------------------------

   Public Functions

---------------------------------------------------------------------------*/

/*-----------------------------------------------------------------------*/
/* Get Disk Status                                                       */
/*-----------------------------------------------------------------------*/

DSTATUS disk_status(
    BYTE drv /* Drive number (always 0) */
)
{
    if (drv)
        return STA_NOINIT;

    return Stat;
}

/*-----------------------------------------------------------------------*/
/* Initialize Disk Drive                                                 */
/*-----------------------------------------------------------------------*/

DSTATUS disk_initialize(
    uint8_t drv /* Physical drive nmuber (0) */
)
{
    (void)drv;
    uint16_t t0 = xTaskGetTickCount();

    // must supply min of 74 clock cycles with CS high.
    card_deselect();
    uint8_t tmp = 0xFF;
    for (uint8_t i = 0; i < 10; i++)
    {
        spiSend(tmp);
    }
    card_select();

    // command to go idle in SPI mode
    for (uint8_t i = 1;; i++)
    {
        if (cardCommand(CMD0, 0) == R1_IDLE_STATE)
        {
            #if SDMMC_DEBUG_PRINT
                printf("Card is idle\r\n");
            #endif
            break;
        }
        else
        {
            #if SDMMC_DEBUG_PRINT
                printf("CMD0 #%u fails\r\n", i);
            #endif
        }
        if (i == SD_CMD0_RETRY)
        {
            printf("Error! SD_CARD_ERROR_CMD0\r\n");
            return STA_NOINIT;
        }
        // stop multi-block write
        spiSend(STOP_TRAN_TOKEN);
        // finish block transfer
        for (int k = 0; k < 520; k++)
        {
            spiReceive();
        }
    }

    // check SD version
    if (cardCommand(CMD8, 0x1AA) == (R1_ILLEGAL_COMMAND | R1_IDLE_STATE))
    {
        #if SDMMC_DEBUG_PRINT
            printf("m_type = SD_CARD_TYPE_SD1\r\n");
        #endif
        m_type = SD_CARD_TYPE_SD1;
    }
    else
    {
        for (uint8_t i = 0; i < 4; i++)
        {
            m_status = spiReceive();
        }
        if (m_status == 0XAA)
        {
            #if SDMMC_DEBUG_PRINT
                printf("m_type = SD_CARD_TYPE_SD2\r\n");
            #endif
            m_type = SD_CARD_TYPE_SD2;
        }
        else
        {
            #if SDMMC_DEBUG_PRINT
                printf("Error! SD_CARD_ERROR_CMD8\r\n");
            #endif
            return STA_NOINIT;
        }
    }

    // initialize card and send host supports SDHC if SD2
    uint32_t arg = m_type == SD_CARD_TYPE_SD2 ? 0X40000000 : 0;

    while (cardAcmd(ACMD41, arg) != R1_READY_STATE)
    {
        // check for timeout
        if (isTimedOut(t0, SD_INIT_TIMEOUT))
        {
            printf("Error! SD_CARD_ERROR_ACMD41\r\n");
            return STA_NOINIT;
        }
    }
    // if SD2 read OCR register to check for SDHC card
    if (m_type == SD_CARD_TYPE_SD2)
    {
        if (cardCommand(CMD58, 0))
        {
            printf("Error! SD_CARD_ERROR_CMD58\r\n");
            return STA_NOINIT;
        }
        if ((spiReceive() & 0XC0) == 0XC0)
        {
            #if SDMMC_DEBUG_PRINT
                printf("m_type = SD_CARD_TYPE_SDHC\r\n");
            #endif
            m_type = SD_CARD_TYPE_SDHC;
        }
        // Discard rest of ocr - contains allowed voltage range.
        for (uint8_t i = 0; i < 3; i++)
        {
            spiReceive();
        }
    }

    
    #if SDMMC_DEBUG_PRINT
        printf("Card initialized\r\n");
    #endif
    Stat = 0;
    card_deselect(); // Keep card seletcted
    return 0;
}

/*-----------------------------------------------------------------------*/
/* Read Sector(s)                                                        */
/*-----------------------------------------------------------------------*/

DRESULT disk_read(
    uint8_t drv,  /* Physical drive nmuber (0) */
    BYTE *buff,   /* Pointer to the data buffer to store read data */
    DWORD sector, /* Start sector number (LBA) */
    UINT count    /* Sector count (1..128) */
)
{
    #if SDMMC_DEBUG_PRINT
        printf("disk_read: drv: %u, sector: %llu, count: %lu\r\n", drv, sector, count);
    #endif
    memset(buff, 0xFF, 512 * count);

    if (disk_status(drv) & STA_NOINIT)
        return RES_NOTRDY;
    card_select();
    if (!readStart(sector))
    {
        printf("Error: readStart(sector)\r\n");
        return false;
    }
    for (uint16_t b = 0; b < count; b++, buff += 512)
    {
        if (!readData(buff, 512))
        {
            printf("Error: readData(buff, 512)\r\n");
            return false;
        }
    }
    if (readStop())
    {
        card_deselect();
        return RES_OK;
    }
    else
    {
        card_deselect();
        return RES_ERROR;
    }
}

/*-----------------------------------------------------------------------*/
/* Write Sector(s)                                                       */
/*-----------------------------------------------------------------------*/

DRESULT disk_write(
    BYTE drv,         /* Physical drive nmuber (0) */
    const BYTE *buff, /* Pointer to the data to be written */
    DWORD sector,     /* Start sector number (LBA) */
    UINT count        /* Sector count (1..128) */
)
{
    if (disk_status(drv) & STA_NOINIT)
        return RES_NOTRDY;

    card_select();
    if (!writeStart(sector))
    {
        printf("Error: writeStart(sector)\r\n");
        return false;
    }
    for (size_t b = 0; b < count; b++, buff += 512)
    {
        if (!writeData((uint8_t *)buff))
        {
            printf("Error: writeData(buff)\r\n");
            return false;
        }
    }
    if (writeStop())
    {
        card_deselect();
        return RES_OK;
    }
    else
    {
        card_deselect();
        return RES_ERROR;
    }
}

/*-----------------------------------------------------------------------*/
/* Miscellaneous Functions                                               */
/*-----------------------------------------------------------------------*/

DRESULT disk_ioctl(
    BYTE drv,  /* Physical drive nmuber (0) */
    BYTE ctrl, /* Control code */
    void *buff /* Buffer to send/receive control data */
)
{
    if (disk_status(drv) & STA_NOINIT)
        return RES_NOTRDY; /* Check if card is in the socket */

    DRESULT res;
    BYTE n, csd[16];
    DWORD cs;

    res = RES_ERROR;
    switch (ctrl)
    {
    case CTRL_SYNC: /* Make sure that no pending write process */
        if (!isBusy())
        {
            res = RES_OK;
        }
        break;

    case GET_SECTOR_COUNT: /* Get number of sectors on the disk (DWORD) */
        configASSERT(readRegister(CMD9, csd));
        if ((csd[0] >> 6) == 1)
        { /* SDC ver 2.00 */
            cs = csd[9] + ((WORD)csd[8] << 8) + ((DWORD)(csd[7] & 63) << 16) + 1;
            *(DWORD *)buff = cs << 10;
        }
        else
        { /* SDC ver 1.XX or MMC */
            n = (csd[5] & 15) + ((csd[10] & 128) >> 7) + ((csd[9] & 3) << 1) + 2;
            cs = (csd[8] >> 6) + ((WORD)csd[7] << 2) + ((WORD)(csd[6] & 3) << 10) + 1;
            *(DWORD *)buff = cs << (n - 9);
        }
        #if SDMMC_DEBUG_PRINT
            printf("Get sector count: %llu\r\n", cs);
        #endif
        res = RES_OK;
        break;

    case GET_BLOCK_SIZE: /* Get erase block size in unit of sector (DWORD) */
        *(DWORD *)buff = 128;
        res = RES_OK;
        break;

    default:
        res = RES_PARERR;
    }

    return res;
}
