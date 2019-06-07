// Modified SIFI driver.
// TODO: add a proper license
#ifndef PLIC_DRIVER_H
#define PLIC_DRIVER_H

#include "stdint.h"

// 32 bits per source
#define PLIC_PRIORITY_OFFSET 0x0000UL
#define PLIC_PRIORITY_SHIFT_PER_SOURCE 2
// 1 bit per source (1 address)
#define PLIC_PENDING_OFFSET 0x1000UL
#define PLIC_PENDING_SHIFT_PER_SOURCE 0

//0x80 per target
#define PLIC_ENABLE_OFFSET 0x2000
#define PLIC_ENABLE_SHIFT_PER_TARGET 7

#define PLIC_THRESHOLD_OFFSET 0x200000UL
#define PLIC_CLAIM_OFFSET 0x200004UL
#define PLIC_THRESHOLD_SHIFT_PER_TARGET 12
#define PLIC_CLAIM_SHIFT_PER_TARGET 12

#define PLIC_MAX_SOURCE 1023
#define PLIC_SOURCE_MASK 0x3FF

#define PLIC_MAX_TARGET 15871
#define PLIC_TARGET_MASK 0x3FFF

//TODO: This might be better in bsp.h
#define PLIC_NUM_INTERRUPTS 16

/**
 * This data type defines an interrupt handler for a device.
 * The argument points to the instance of the component
 */
typedef void (*plic_interrupt_handler_t)(void *InstancePtr);

/* The following data type defines each entry in an interrupt vector table.
 * The callback reference is the base address of the interrupting device
 * for the driver interface given in this file and an instance pointer for the
 * driver interface given in xintc.h file.
 */
typedef struct
{
  plic_interrupt_handler_t Handler;
  void *CallBackRef;
} plic_VectorTableEntry;

typedef struct __plic_instance_t
{
  uintptr_t base_addr;

  uint32_t num_sources;
  uint32_t num_priorities;
  plic_VectorTableEntry HandlerTable[PLIC_NUM_INTERRUPTS];

} plic_instance_t;

typedef uint32_t plic_source;
typedef uint32_t plic_priority;
typedef uint32_t plic_threshold;

void PLIC_init(
    plic_instance_t *this_plic,
    uintptr_t base_addr,
    uint32_t num_sources,
    uint32_t num_priorities);

void PLIC_set_threshold(plic_instance_t *this_plic,
                        plic_threshold threshold);

void PLIC_enable_interrupt(plic_instance_t *this_plic,
                           plic_source source);

void PLIC_disable_interrupt(plic_instance_t *this_plic,
                            plic_source source);

void PLIC_set_priority(plic_instance_t *this_plic,
                       plic_source source,
                       plic_priority priority);

plic_source PLIC_claim_interrupt(plic_instance_t *this_plic);

void PLIC_complete_interrupt(plic_instance_t *this_plic,
                             plic_source source);

plic_source PLIC_register_interrupt_handler(plic_instance_t *this_plic, plic_source source_id, plic_interrupt_handler_t handler, void *CallBackRef);

void PLIC_unregister_interrupt_handler(plic_instance_t *this_plic, plic_source source_id);

#endif
