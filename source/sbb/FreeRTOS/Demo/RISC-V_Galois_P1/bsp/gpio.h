#ifndef __GPIO_H__
#define __GPIO_H__

#include <stdint.h>
#include "bsp.h"

#if BSP_USE_GPIO

/**
 * Initialize GPIO driver
 */
void gpio_init(void);

/**
 * Set GPIO_1 index `i` as output
 * @assert 0 <= i <= 7
 */
void gpio_set_as_output(uint8_t i);

/**
 * Set GPIO_1 index `i` as input
 * @assert 0 <= i <= 7
 */
void gpio_set_as_input(uint8_t i);

/**
 * Set GPIO_1 index `i`
 * @assert 0 <= i <= 7
 */
void gpio_write(uint8_t i);

/**
 * Clear GPIO_1 index `i`
 * @assert 0 <= i <= 7
 */
void gpio_clear(uint8_t i);

/**
 * Read GPIO_1 index `i`
 * @assert 0 <= i <= 7
 */
uint8_t gpio_read(uint8_t i);

/**
 * Turn on LED 0-7
 * Onboard LEDs are on GPIO_1 bank 2
 */
void led_write(uint8_t i);

/**
 * Turn off LED 0-7
 * Onboard LEDs are on GPIO_1 bank 2
 */
void led_clear(uint8_t i);
#endif

#endif /* __GPIO_H__ */