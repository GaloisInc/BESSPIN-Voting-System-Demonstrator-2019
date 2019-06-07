#if !BSP_USE_GPIO
#include "gpio.h"
#include "xgpio.h"
#include "bsp.h"

#define GPIO1_MAX 7
#define LED_MAX 7
#define GPIO_CHANNEL 1
#define LED_CHANNEL 2

XGpio Device; /* Xilinx GPIO driver */

/**
 * Initialize GPIO driver
 */
void gpio_init(void) {
	configASSERT(XGpio_Initialize(&Device, XPAR_GPIO_0_DEVICE_ID) == XST_SUCCESS);
}

/**
 * Set GPIO_1 index `i` as output
 * Bits set to 0 are output
 * @assert 0 <= i <= 7
 */
void gpio_set_as_output(uint8_t i) {
	configASSERT(i <= GPIO1_MAX);
	uint32_t mask = XGpio_GetDataDirection(&Device, GPIO_CHANNEL);
	mask &= ~(1 << i);
	XGpio_SetDataDirection(&Device, GPIO_CHANNEL, mask);
}

/**
 * Set GPIO_1 index `i` as input
 * Bits set to 1 are input
 * @assert 0 <= i <= 7
 */
void gpio_set_as_input(uint8_t i) {
	configASSERT(i <= GPIO1_MAX);
	uint32_t mask = XGpio_GetDataDirection(&Device, GPIO_CHANNEL);
	mask |= (1 << i);
	XGpio_SetDataDirection(&Device, GPIO_CHANNEL, mask);
}

/**
 * Set GPIO_1 index `i`
 * @assert 0 <= i <= 7
 */
void gpio_write(uint8_t i) {
	configASSERT(i <= GPIO1_MAX);
	uint32_t mask = XGpio_DiscreteRead(&Device, GPIO_CHANNEL);
	mask |= (1 << i);
	XGpio_DiscreteWrite(&Device, GPIO_CHANNEL, mask);
}

/**
 * Clear GPIO_1 index `i`
 * @assert 0 <= i <= 7
 */
void gpio_clear(uint8_t i) {
	configASSERT(i <= GPIO1_MAX);
	uint32_t mask = XGpio_DiscreteRead(&Device, GPIO_CHANNEL);
	mask &= ~(1 << i);
	XGpio_DiscreteWrite(&Device, GPIO_CHANNEL, mask);
}

/**
 * Read GPIO_1 index `i`
 * @assert 0 <= i <= 7
 */
uint8_t gpio_read(uint8_t i) {
	configASSERT(i <= GPIO1_MAX);
	uint32_t value = XGpio_DiscreteRead(&Device, GPIO_CHANNEL);
	return (value >> i) & 0x1;
}

/**
 * Turn on LED 0-7
 * Onboard LEDs are on GPIO_1 bank 2
 */
void led_write(uint8_t i) {
	configASSERT(i <= LED_MAX);
	uint32_t mask = XGpio_DiscreteRead(&Device, LED_CHANNEL);
	mask |= (1 << i);
	XGpio_DiscreteWrite(&Device, LED_CHANNEL, mask);
}

/**
 * Turn off LED 0-7
 * Onboard LEDs are on GPIO_1 bank 2
 */
void led_clear(uint8_t i) {
	configASSERT(i <= LED_MAX);
	uint32_t mask = XGpio_DiscreteRead(&Device, LED_CHANNEL);
	mask &= ~(1 << i);
	XGpio_DiscreteWrite(&Device, LED_CHANNEL, mask);
}

#endif