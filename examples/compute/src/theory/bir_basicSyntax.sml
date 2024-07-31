(* ------------------------------------------------------------------------- *)
(*  Syntax function regarding basic BIR typing                               *)
(* ------------------------------------------------------------------------- *)


structure bir_basicSyntax :> bir_basicSyntax =
struct

open HolKernel Parse bossLib boolLib ;

val ERR = mk_HOL_ERR "bir_basicSyntax" ;



val val_imm_tm = prim_mk_const{Name="BVal_Imm", Thy="bir_basic"} ;
val val_mem_tm = prim_mk_const{Name="BVal_Mem", Thy="bir_basic"} ;



fun dest_val_imm (tm:term) : term =
  dest_monop val_imm_tm (ERR "dest_val_imm" "not BVal_Imm") tm

fun dest_val_mem (tm:term) : term * term * term =
  dest_triop val_mem_tm (ERR "dest_val_mem" "not BVal_Mem") tm



fun is_val_imm (tm: term) : bool = 
  can dest_val_imm tm

fun is_val_mem (tm: term) : bool = 
  can dest_val_mem tm




end
