open HolKernel bossLib boolLib Parse;
open driver_stateTheory driver_callTheory driver_writeTheory driver_readTheory driver_checkTheory driver_relationTheory;
open bslSyntax;
open examplesBinaryTheory;

val _ = new_theory "bir_driver_weak_bisim";

(* define the pre and post conditions for code segment B *)
(* BIR variables*)
val get_ch0conf = bden (bvar "R4" ``(BType_Imm Bit64)``);

(* BIR constants *)
val get_v = bconst ``v:word64``;
val get_v1 = bconst ``0xFFEFCFFFw:word64``;
val get_v2 = bconst ``0x100000w:word64``;

val bir_driver_segB_precond_def = Define `
bir_driver_segB_procond v = ^(beq(get_ch0conf,get_v))`

val bir_driver_segB_postcond_def = Define `
bir_driver_segB_postcond v = 
^(beq(get_ch0conf, 
      bor(band(get_v,get_v1),get_v2)))`


val _ = export_theory();
