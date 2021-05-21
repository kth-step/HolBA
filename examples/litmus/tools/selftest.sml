open HolKernel Parse boolLib bossLib;

open herdLitmusLib UtilLib;

val test = "RISCV testname\n {\n x=1; y=2; 0:x1=1; 1:x1=2; 0:x2=x; 1:x2=y; 0:x3=y; 1:x3=x; \n }  \n"
	 ^ "P0 | P1; \n"
	 ^ "sw x1, 0(x2) | sw x1, 0(x2); \n"
	 ^ "lw x4, 0(x3) | lw x4, 0(x3); \n"
         ^ "exists(0:x4=2 /\\ 1:x4=1)";

val litmus = parse test;

(* TODO: Self tests *)

