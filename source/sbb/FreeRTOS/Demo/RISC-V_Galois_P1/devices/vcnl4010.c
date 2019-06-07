#include "vcnl4010.h"

// the i2c address
#define VCNL4010_I2CADDR_DEFAULT 0x13

// commands and constants
#define VCNL4010_COMMAND 0x80
#define VCNL4010_PRODUCTID 0x81
#define VCNL4010_PROXRATE 0x82
#define VCNL4010_IRLED 0x83
#define VCNL4010_AMBIENTPARAMETER 0x84
#define VCNL4010_AMBIENTDATA 0x85
#define VCNL4010_PROXIMITYDATA 0x87
#define VCNL4010_INTCONTROL 0x89
#define VCNL4010_PROXINITYADJUST 0x8A
#define VCNL4010_INTSTAT 0x8E
#define VCNL4010_MODTIMING 0x8F

#define VCNL4010_MEASUREAMBIENT 0x10
#define VCNL4010_MEASUREPROXIMITY 0x08
#define VCNL4010_AMBIENTREADY 0x40
#define VCNL4010_PROXIMITYREADY 0x20

#define VCNL4010_16_625 3

static void vcnl4010_write_u8(struct IicDriver *Iic, uint8_t addr, uint8_t values);
static uint8_t vcnl4010_read_u8(struct IicDriver *Iic, uint8_t addr);
static uint8_t vcnl4010_read_u16(struct IicDriver *Iic, uint8_t addr);

static void vcnl4010_write_u8(struct IicDriver *Iic, uint8_t addr, uint8_t values)
{
    uint8_t data[2] = {addr, values};
    configASSERT(iic_transmit(Iic, VCNL4010_I2CADDR_DEFAULT, data, 2) != -1);
}

static uint8_t vcnl4010_read_u8(struct IicDriver *Iic, uint8_t addr)
{
    uint8_t data;
    data = addr;
    configASSERT(iic_transmit(Iic, VCNL4010_I2CADDR_DEFAULT, &data, 1) != -1);
    vTaskDelay(pdMS_TO_TICKS(10)); // requires 170us delay
    configASSERT(iic_receive(Iic, VCNL4010_I2CADDR_DEFAULT, &data, 1) != -1);
    return data;
}

static uint8_t vcnl4010_read_u16(struct IicDriver *Iic, uint8_t addr)
{
    uint8_t data[2] = {0};
    data[0] = addr;
    configASSERT(iic_transmit(Iic, VCNL4010_I2CADDR_DEFAULT, data, 1) != -1);
    vTaskDelay(pdMS_TO_TICKS(10));
    configASSERT(iic_receive(Iic, VCNL4010_I2CADDR_DEFAULT, data, 2) != -1);
    return (uint16_t)(data[0] << 8 | data[1]);
}

bool vcnl4010_init(struct Vcnl4010_t *sensor, struct IicDriver *bus)
{
    sensor->bus = bus;
    uint8_t rev = vcnl4010_read_u8(sensor->bus, VCNL4010_PRODUCTID);
    if ((rev & 0xF0) != 0x20)
    {
        return false;
    }

    vcnl4010_write_u8(sensor->bus, VCNL4010_IRLED, 20);
    vcnl4010_write_u8(sensor->bus, VCNL4010_MODTIMING, VCNL4010_16_625);
    vcnl4010_write_u8(sensor->bus, VCNL4010_INTCONTROL, 0x08);
    return true;
}

uint16_t vcnl4010_readProximity(struct Vcnl4010_t *sensor)
{
    uint8_t i = vcnl4010_read_u8(sensor->bus, VCNL4010_INTSTAT);
    i &= ~0x80;
    vcnl4010_write_u8(sensor->bus, VCNL4010_INTSTAT, i);

    vcnl4010_write_u8(sensor->bus, VCNL4010_COMMAND, VCNL4010_MEASUREPROXIMITY);
    while (1)
    {
        uint8_t result = vcnl4010_read_u8(sensor->bus, VCNL4010_COMMAND);
        if (result & VCNL4010_PROXIMITYREADY)
        {
            return vcnl4010_read_u16(sensor->bus, VCNL4010_PROXIMITYDATA);
        }
        vTaskDelay(pdMS_TO_TICKS(10));
    }
}

uint16_t vcnl4010_readAmbient(struct Vcnl4010_t *sensor)
{
    uint8_t i = vcnl4010_read_u8(sensor->bus, VCNL4010_INTSTAT);
    i &= ~0x40;
    vcnl4010_write_u8(sensor->bus, VCNL4010_INTSTAT, i);
    vcnl4010_write_u8(sensor->bus, VCNL4010_COMMAND, VCNL4010_MEASUREAMBIENT);
    while (1)
    {
        uint8_t result = vcnl4010_read_u8(sensor->bus, VCNL4010_COMMAND);
        if (result & VCNL4010_AMBIENTREADY)
        {
            return vcnl4010_read_u16(sensor->bus, VCNL4010_AMBIENTDATA);
        }
        vTaskDelay(pdMS_TO_TICKS(100));
    }
}
