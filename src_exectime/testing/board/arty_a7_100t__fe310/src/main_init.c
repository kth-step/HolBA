#include "uart.h"
#include <stdint.h>

int main();

/* memory init code */
extern uint32_t _data_lma;
extern uint32_t _data;
extern uint32_t _edata;
extern uint32_t _bss;
extern uint32_t _ebss;

void _env_mem_init()
{
    uint32_t read_from, write_to, section_len;
    read_from   = (uint32_t)&_data_lma;
    write_to    = (uint32_t)&_data;
    section_len = ((uint32_t)&_edata) - write_to;

    uint32_t i;
    for (i = 0; i < section_len; i += 4)
    {
        *((uint32_t*)write_to) = *((uint32_t*)read_from);
        write_to += 4;
        read_from += 4;
    }

    write_to    = (uint32_t)&_bss;
    section_len = ((uint32_t)&_ebss) - write_to;

    for (i = 0; i < section_len; i += 4)
    {
        *((uint32_t*)write_to) = 0;
        write_to += 4;
    }
}

/* overall init function */
int _main_init()
{
    _env_mem_init();
    uart_init();

    return main();
}


