/*
 * Derived from code:
 * 
 * https://github.com/dwelch67/sifive_samples/blob/master/hifive1/uart03/novectors.s
 */


.globl dummy
dummy:
    ret

.globl PUT32
PUT32:
    sw x11,(x10)
    ret

.globl GET32
GET32:
    lw x10,(x10)
    ret

.globl MCYCLE
MCYCLE:
    csrr x10,mcycle
    ret

.globl AMOSWAP
AMOSWAP:
    amoswap.w x10, x11, (x10)
    ret


