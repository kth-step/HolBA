#include "uart.h"
#include "lib/printf.h"

#include <stdint.h>

void printf_init() {
  uart_init();
}

void printf_echoloop()
{
  uart_echoloop();
}


static void printf_string(char *str)
{
    if(!str) str = "(null)";    
    uart_print_string(str);
}

static void printf_int(int i)
{
    int f = 0, neg = 0;
    char buffer[28];
    
    if(i < 0) {
        neg ++;
        i = - i;
    }
    do {
        buffer[f++] = '0' + (i % 10);
        i /= 10;
    } while(i);
    
    if(neg) buffer[f++] = '-';
    
    while(f) {
        uart_putchar( buffer[--f]);
    }
}

static void printf_hex(uint32_t n, int size)
{
    uint64_t h;
    int i;
    
    for(i = size * 8; i; ) {
        i -= 4;
        h = (n >> i) & 15;
        
        if(h < 10) h += '0';
        else h += 'A' - 10;
        
        uart_putchar(h);
    }
}

static void printf_bin(uint32_t n)
{
    int i;
    for(i = 32; i != 0; i--) {
        if( (i != 32) && !(i & 3)) uart_putchar('_');
        uart_putchar( (n >> 31) ? '1' : '0');
        n <<= 1;
    }
}

// -----------------------------------
void printf(const char *fmt, ...)
{
    int c;
    va_list args;    
    va_start(args, fmt);
        
    for(;;) {
        c = *fmt;
        if(c == '\0') goto cleanup;
        
        fmt ++;
        if(c == '%') {
            c = *fmt;
            fmt++;
            
            // sanity check?
            if(c == '\0') {
                uart_putchar(c);
                goto cleanup;
            }
            
            switch(c) {
            case 'c':
                uart_putchar(va_arg(args, int));
                break;
            case 's':
                printf_string(va_arg(args, char *));
                break;
            case 'i':
            case 'd':
                printf_int(va_arg(args, int));
                break;
            case 'x':
                printf_hex(va_arg(args, uint32_t), 4);
                break;                
            case 'b':
                printf_bin(va_arg(args, uint32_t));
                break;
            case '%':
                uart_putchar(c);
                break;
            default:
                uart_putchar('%');
                uart_putchar(c);
            }
            
        } else uart_putchar(c);
    }
       
    /* yes, gotos are evil. we know */
cleanup:
    va_end(args);
}

