#include "uart.h"
#include "lib/printf.h"
#include <stdint.h>

void experiment_complete_marker();

void do_bad_sync() {
  uart_print_string("EXCEPTION: do_bad_sync\n");
  experiment_complete_marker();
  while (1);
}

void do_bad_irq() {
  uart_print_string("EXCEPTION: do_bad_irq\n");
  experiment_complete_marker();
  while (1);
}

void do_bad_fiq() {
  uart_print_string("EXCEPTION: do_bad_fiq\n");
  experiment_complete_marker();
  while (1);
}

void do_bad_error() {
  uart_print_string("EXCEPTION: do_bad_error\n");
  experiment_complete_marker();
  while (1);
}

void do_sync() {
  uint64_t esr_;
  asm (
       "MRS %x[result], ESR_EL3"
       : [result] "=r" (esr_)
       : 
       );
  //https://developer.arm.com/documentation/ddi0595/2020-12/AArch64-Registers/ESR-EL1--Exception-Syndrome-Register--EL1-
  uart_print_string("EXCEPTION: do_sync\n");
  printf("ESR_EL3 = 0x%x\n", esr_);
  experiment_complete_marker();
  while (1);
}

void do_irq() {
  uart_print_string("EXCEPTION: do_irq\n");
  experiment_complete_marker();
  while (1);
}

void do_fiq() {
  uart_print_string("EXCEPTION: do_fiq\n");
  experiment_complete_marker();
  while (1);
}

void do_error() {
  uart_print_string("EXCEPTION: do_error\n");
  experiment_complete_marker();
  while (1);
}


