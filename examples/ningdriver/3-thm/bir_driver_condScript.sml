open HolKernel bossLib boolLib Parse;
open examplesBinaryTheory bslSyntax;


val _ = new_theory "bir_driver_cond";

(* define the pre and post conditions for code segment B *)
(* BIR variables*)
val get_ch0conf_ad = bden (bvar "R4" ``(BType_Imm Bit64)``);
val get_ch0conf_v_pre = bden (bvar "R9" ``(BType_Imm Bit64)``);
val get_ch0conf_v_post = bden (bvar "R5" ``(BType_Imm Bit64)``);

(* BIR constants *)
val get_v = bconst ``v:word64``;
val get_v1 = bconst ``0xFFEFCFFFw:word64``;
val get_v2 = bconst ``0x100000w:word64``;
val get_ad = bconst ``0xFA03012Cw:word64``;

val bir_driver_segB_precond_def = Define `
bir_driver_segB_procond v = ^(beq(get_ch0conf_v_pre,get_v))`

val bir_driver_segB_postcond_def = Define `
bir_driver_segB_postcond v = 
^(band(beq(get_ch0conf_ad,get_ad),
       beq(get_ch0conf_v_post, 
           bor(band(get_v,get_v1),get_v2))))`

val bir_driver_segB_post_def = Define `
bir_driver_segB_post v =
\l. if (l = BL_Address (Imm64 0x60w))
                        then bir_driver_segB_postcond v
                        else bir_exp_false`

val _ = export_theory();
