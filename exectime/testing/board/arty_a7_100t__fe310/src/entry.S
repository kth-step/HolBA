
.globl _embexp_entry
_embexp_entry:
    /* Set registers to a defined state */
    mv x1,  x0
    mv x2,  x0
    mv x3,  x0
    mv x4,  x0
    mv x5,  x0
    mv x6,  x0
    mv x7,  x0
    mv x8,  x0
    mv x9,  x0
    mv x10, x0
    mv x11, x0
    mv x12, x0
    mv x13, x0
    mv x14, x0
    mv x15, x0
    mv x16, x0
    mv x17, x0
    mv x18, x0
    mv x19, x0
    mv x20, x0
    mv x21, x0
    mv x22, x0
    mv x23, x0
    mv x24, x0
    mv x25, x0
    mv x26, x0
    mv x27, x0
    mv x28, x0
    mv x29, x0
    mv x30, x0
    mv x31, x0
    csrw mtvec,    x0
    csrw mstatus,  x0
    csrw mie,      x0
    csrw mip,      x0
    csrw mcause,   x0
    csrw mepc,     x0
    csrw mtval,    x0
    csrw mscratch, x0

    /* Setup the stack pointer. */
    la sp, __stack_pointer$

    /* Setup simple trap vector */
    la t0, _hang
    csrw mtvec, t0

    /* Call c init code */
    call _main_init

    /* hang if we end up here again */
    j _hang


.globl _hang
_hang:
    ebreak
    j _hang


