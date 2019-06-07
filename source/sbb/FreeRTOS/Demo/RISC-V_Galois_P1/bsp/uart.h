#ifndef __UART_16550_H__
#define __UART_16550_H__

#include "bsp.h"
#include <stdbool.h>

#if BSP_USE_UART0
bool uart0_rxready(void);
char uart0_rxchar(void);
char uart0_txchar(char c);
int uart0_rxbuffer(char *ptr, int len);
int uart0_txbuffer(char *ptr, int len);
void uart0_init(void);
#endif

#if BSP_USE_UART1
bool uart1_rxready(void);
char uart1_rxchar(void);
char uart1_txchar(char c);
int uart1_rxbuffer(char *ptr, int len);
int uart1_txbuffer(char *ptr, int len);
void uart1_init(void);
#endif

#endif
