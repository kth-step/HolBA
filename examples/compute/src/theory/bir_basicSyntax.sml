(* ------------------------------------------------------------------------- *)
(*  Syntax function regarding basic BIR typing                               *)
(* ------------------------------------------------------------------------- *)


structure bir_basicSyntax :> bir_basicSyntax =
struct

open HolKernel Parse bossLib boolLib ;

val ERR = mk_HOL_ERR "bir_basicSyntax" ;



val val_imm_tm = prim_mk_const{Name="BVal_Imm", Thy="bir_basic"} ;
val val_mem_tm = prim_mk_const{Name="BVal_Mem", Thy="bir_basic"} ;
val exp_const_tm = prim_mk_const{Name="BExp_Const", Thy="bir_basic"} ;
val exp_mem_const_tm = prim_mk_const{Name="BExp_MemConst", Thy="bir_basic"} ;
val exp_den_tm = prim_mk_const{Name="BExp_Den", Thy="bir_basic"} ;
val exp_bin_exp_tm = prim_mk_const{Name="BExp_BinExp", Thy="bir_basic"} ;
val exp_unary_exp_tm = prim_mk_const{Name="BExp_UnaryExp", Thy="bir_basic"} ;
val exp_bin_pred_tm = prim_mk_const{Name="BExp_BinPred", Thy="bir_basic"} ;
val exp_if_then_else_tm = prim_mk_const{Name="BExp_IfThenElse", Thy="bir_basic"} ;
val exp_load_tm = prim_mk_const{Name="BExp_Load", Thy="bir_basic"} ;
val exp_store_tm = prim_mk_const{Name="BExp_Store", Thy="bir_basic"} ;



fun dest_val_imm (tm:term) : term =
  dest_monop val_imm_tm (ERR "dest_val_imm" "not BVal_Imm") tm

fun dest_val_mem (tm:term) : term * term * term =
  dest_triop val_mem_tm (ERR "dest_val_mem" "not BVal_Mem") tm

fun dest_exp_const (tm:term) : term =
  dest_monop exp_const_tm (ERR "dest_exp_const" "not BExp_Const") tm

fun dest_exp_mem_const (tm:term) : (term * term * term) =
  dest_triop exp_mem_const_tm (ERR "dest_exp_mem_const" "not BExp_MemConst") tm

fun dest_exp_den (tm:term) : term  =
  dest_monop exp_den_tm (ERR "dest_exp_den" "not BExp_Den") tm

fun dest_exp_bin_exp (tm:term) : (term * term * term) =
  dest_triop exp_bin_exp_tm (ERR "dest_exp_bin_exp" "not BExp_BinExp") tm

fun dest_exp_unary_exp (tm:term) : (term * term) =
  dest_binop exp_unary_exp_tm (ERR "dest_exp_unary_exp" "not BExp_UnaryExp") tm

fun dest_exp_bin_pred (tm:term) : (term * term * term) = 
  dest_triop exp_bin_pred_tm (ERR "dest_exp_bin_pred" "not BExp_BinPred") tm

fun dest_exp_if_then_else (tm:term) : (term * term * term)  =
  dest_triop exp_if_then_else_tm (ERR "dest_exp_if_then_else" "not BExp_IfThenElse") tm

fun dest_exp_load (tm:term) : (term * term * term * term)  =
  dest_quadop exp_load_tm (ERR "dest_exp_load" "not BExp_Load") tm

fun dest_exp_store (tm:term) : (term * term * term * term)  =
  dest_quadop exp_store_tm (ERR "dest_exp_store" "not BExp_Store") tm


fun is_val_imm (tm: term) : bool = 
  can dest_val_imm tm

fun is_val_mem (tm: term) : bool = 
  can dest_val_mem tm

fun is_exp_const (tm: term) : bool =
  can dest_exp_const tm

fun is_exp_mem_const (tm: term) : bool =
  can dest_exp_mem_const tm

fun is_exp_den (tm: term) : bool =
  can dest_exp_den tm

fun is_exp_bin_exp (tm: term) : bool =
  can dest_exp_bin_exp tm

fun is_exp_unary_exp (tm: term) : bool =
  can dest_exp_unary_exp tm

fun is_exp_bin_pred (tm: term) : bool =
  can dest_exp_bin_pred tm

fun is_exp_if_then_else (tm: term) : bool =
  can dest_exp_if_then_else tm

fun is_exp_load (tm: term) : bool =
  can dest_exp_load tm

fun is_exp_store (tm: term) : bool =
  can dest_exp_store tm




end
