#ifndef __VCNL4010_H__
#define __VCNL4010_H__

#include <stdbool.h>
#include "iic.h"

struct Vcnl4010_t
{
    struct IicDriver *bus;
};

bool vcnl4010_init(struct Vcnl4010_t *sensor, struct IicDriver *Iic);
uint16_t vcnl4010_readProximity(struct Vcnl4010_t *sensor);
uint16_t vcnl4010_readAmbient(struct Vcnl4010_t *sensor);

#endif /* __VCNL4010_H__ */