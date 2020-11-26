
open HolKernel Parse;

open bir_quotationLib;

val ex1 =
BIR
`start:
x0=x1
jmp next;

next:
x1=2+MEM[x0]
MEM=MEM{x0:=(w1:Bit8)}
halt x0`;

val ex2 =
BIR
`start:
x0=MEM[x1-1]+2
jmp next;

next:
halt x0`;

val expr = BExp`(x0:Bit8)+MEM[x0]`;


``t = ^(BExp`x0*x1`)``
