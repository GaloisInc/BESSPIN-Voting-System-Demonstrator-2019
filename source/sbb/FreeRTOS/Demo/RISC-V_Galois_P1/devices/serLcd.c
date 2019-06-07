#include "serLcd.h"
#include <string.h>

#define LCD_USE_SPI 0

#if LCD_USE_SPI
#include "spi.h"
#include <stdio.h>
#define LCD_SPI_SLAVE_IDX 1
#else
#include "iic.h"
#define LCD_DEFAULT_BUS Iic0     // Default iic bus
#define LCD_DEFAULT_ADDRESS 0x72 //This is the default address of the OpenLCD
#endif

#define LCD_MAX_STRLEN 16        // Max length of the text


uint8_t cmd_mode[] = {
    '|',
    '-',
};

void serLcdPrintf(char *str, uint8_t len)
{
    if (len > LCD_MAX_STRLEN)
    {
        len = LCD_MAX_STRLEN;
    }
#if LCD_USE_SPI
    configASSERT(spi1_transmit(LCD_SPI_SLAVE_IDX, cmd_mode, sizeof(cmd_mode)) != -1);
    vTaskDelay(pdMS_TO_TICKS(100));
    configASSERT(spi1_transmit(LCD_SPI_SLAVE_IDX, (uint8_t*)str, len) != -1);
#else
    configASSERT(iic_transmit(&LCD_DEFAULT_BUS, LCD_DEFAULT_ADDRESS, cmd_mode, sizeof(cmd_mode)) != -1);
    vTaskDelay(pdMS_TO_TICKS(100));
    configASSERT(iic_transmit(&LCD_DEFAULT_BUS, LCD_DEFAULT_ADDRESS, (uint8_t *)str, len) != -1);
#endif
}
