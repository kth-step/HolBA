#ifndef _PRINTF_H
#define _PRINTF_H

#include <stdarg.h>

void printf_init();

void printf_echoloop();
void printf(const char *fmt, ...);

#endif
