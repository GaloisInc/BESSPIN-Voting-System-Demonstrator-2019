// Modified SIFI driver.
// TODO: add a proper license
#include "plic_driver.h"
#include <string.h>

// Note that there are no assertions or bounds checking on these
// parameter values.
static void volatile_memzero(uint8_t *base, unsigned int size);

static void volatile_memzero(uint8_t *base, unsigned int size)
{
    volatile uint8_t *ptr;
    for (ptr = base; ptr < (base + size); ptr++)
    {
        *ptr = 0;
    }
}

void PLIC_init(
    plic_instance_t *this_plic,
    uintptr_t base_addr,
    uint32_t num_sources,
    uint32_t num_priorities)
{

    this_plic->base_addr = base_addr;
    this_plic->num_sources = num_sources;
    this_plic->num_priorities = num_priorities;

    // Erase handler table
    for (uint8_t idx = 0; idx < PLIC_NUM_INTERRUPTS; idx++)
    {
        this_plic->HandlerTable[idx].Handler = NULL;
    }

    // Disable all interrupts (don't assume that these registers are reset).
    volatile_memzero((uint8_t *)(this_plic->base_addr +
                                 PLIC_ENABLE_OFFSET),
                     (num_sources + 8) / 8);

    // Set all priorities to 0 (equal priority -- don't assume that these are reset).
    volatile_memzero((uint8_t *)(this_plic->base_addr +
                                 PLIC_PRIORITY_OFFSET),
                     (num_sources + 1) << PLIC_PRIORITY_SHIFT_PER_SOURCE);

    // Set the threshold to 0.
    volatile plic_threshold *threshold = (plic_threshold *)(this_plic->base_addr +
                                                            PLIC_THRESHOLD_OFFSET);

    *threshold = 0;
}

void PLIC_set_threshold(plic_instance_t *this_plic,
                        plic_threshold threshold)
{

    volatile plic_threshold *threshold_ptr = (plic_threshold *)(this_plic->base_addr +
                                                                PLIC_THRESHOLD_OFFSET);

    *threshold_ptr = threshold;
}

void PLIC_enable_interrupt(plic_instance_t *this_plic, plic_source source)
{

    volatile uint8_t *current_ptr = (volatile uint8_t *)(this_plic->base_addr +
                                                         PLIC_ENABLE_OFFSET +
                                                         (source >> 3));
    uint8_t current = *current_ptr;
    current = current | (1 << (source & 0x7));
    *current_ptr = current;
}

void PLIC_disable_interrupt(plic_instance_t *this_plic, plic_source source)
{

    volatile uint8_t *current_ptr = (volatile uint8_t *)(this_plic->base_addr +
                                                         PLIC_ENABLE_OFFSET +
                                                         (source >> 3));
    uint8_t current = *current_ptr;
    current = current & ~((1 << (source & 0x7)));
    *current_ptr = current;
}

void PLIC_set_priority(plic_instance_t *this_plic, plic_source source, plic_priority priority)
{

    if (this_plic->num_priorities > 0)
    {
        volatile plic_priority *priority_ptr = (volatile plic_priority *)(this_plic->base_addr +
                                                                          PLIC_PRIORITY_OFFSET +
                                                                          (source << PLIC_PRIORITY_SHIFT_PER_SOURCE));
        *priority_ptr = priority;
    }
}

plic_source PLIC_claim_interrupt(plic_instance_t *this_plic)
{

    volatile plic_source *claim_addr = (volatile plic_source *)(this_plic->base_addr +
                                                                PLIC_CLAIM_OFFSET);

    return *claim_addr;
}

void PLIC_complete_interrupt(plic_instance_t *this_plic, plic_source source)
{

    volatile plic_source *claim_addr = (volatile plic_source *)(this_plic->base_addr +
                                                                PLIC_CLAIM_OFFSET);
    *claim_addr = source;
}

plic_source PLIC_register_interrupt_handler(plic_instance_t *this_plic, plic_source source_id,
                                            plic_interrupt_handler_t handler,
                                            void *CallBackRef)
{
    if ((source_id >= 1) && (source_id < PLIC_NUM_INTERRUPTS))
    {
        // check if we have a handle registered
        if (this_plic->HandlerTable[source_id].Handler == NULL)
        {
            // register new handler a callback reference
            this_plic->HandlerTable[source_id].Handler = handler;
            this_plic->HandlerTable[source_id].CallBackRef = CallBackRef;
            // enable interrupt
            PLIC_enable_interrupt(this_plic, source_id);
            return source_id;
        }
    }
    // invalid source_id or the source already has a handler
    return 0;
}

void PLIC_unregister_interrupt_handler(plic_instance_t *this_plic, plic_source source_id)
{
    if ((source_id >= 1) && (source_id < PLIC_NUM_INTERRUPTS))
    {
        PLIC_disable_interrupt(this_plic, source_id);
        this_plic->HandlerTable[source_id].Handler = NULL;
    }
}