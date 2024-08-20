(* ------------------------------------------------------------------------- *)
(*  Syntax function regarding basic BIR typing                               *)
(* ------------------------------------------------------------------------- *)


structure bir_cv_basicSyntax :> bir_cv_basicSyntax =
struct

open HolKernel Parse bossLib boolLib;
open bir_cv_basicTheory;

val ERR = mk_HOL_ERR "bir_cv_basicSyntax";



val cv_val_imm_tm = prim_mk_const{Name="BCVVal_Imm", Thy="bir_cv_basic"};
val cv_val_mem_tm = prim_mk_const{Name="BCVVal_Mem", Thy="bir_cv_basic"};
val cv_exp_const_tm = prim_mk_const{Name="BCVExp_Const", Thy="bir_cv_basic"};
val cv_exp_mem_const_tm = prim_mk_const{Name="BCVExp_MemConst", Thy="bir_cv_basic"};
val cv_exp_den_tm = prim_mk_const{Name="BCVExp_Den", Thy="bir_cv_basic"};
val cv_exp_bin_exp_tm = prim_mk_const{Name="BCVExp_BinExp", Thy="bir_cv_basic"};
val cv_exp_unary_exp_tm = prim_mk_const{Name="BCVExp_UnaryExp", Thy="bir_cv_basic"};
val cv_exp_bin_pred_tm = prim_mk_const{Name="BCVExp_BinPred", Thy="bir_cv_basic"};
val cv_exp_if_then_else_tm = prim_mk_const{Name="BCVExp_IfThenElse", Thy="bir_cv_basic"};
val cv_exp_load_tm = prim_mk_const{Name="BCVExp_Load", Thy="bir_cv_basic"};
val cv_exp_store_tm = prim_mk_const{Name="BCVExp_Store", Thy="bir_cv_basic"};


fun mk_cv_val_imm tm =
  list_mk_comb (cv_val_imm_tm, [tm]);

fun mk_cv_val_mem (tm1,tm2,tm3) =
  list_mk_comb (cv_val_mem_tm, [tm1, tm2, tm3]);

fun mk_cv_exp_const tm =
  list_mk_comb (cv_exp_const_tm, [tm]);

fun mk_cv_exp_mem_const (tm1,tm2,tm3) =
  list_mk_comb (cv_exp_mem_const_tm, [tm1, tm2, tm3]);

fun mk_cv_exp_den tm =
  list_mk_comb (cv_exp_den_tm, [tm]);

fun mk_cv_exp_bin_exp (tm1,tm2,tm3) =
  list_mk_comb (cv_exp_bin_exp_tm, [tm1, tm2, tm3]);

fun mk_cv_exp_unary_exp (tm1,tm2) =
  list_mk_comb (cv_exp_unary_exp_tm, [tm1, tm2]);

fun mk_cv_exp_bin_pred (tm1,tm2,tm3) =
  list_mk_comb (cv_exp_bin_pred_tm, [tm1, tm2, tm3]);

fun mk_cv_exp_if_then_else (tm1,tm2,tm3) =
  list_mk_comb (cv_exp_if_then_else_tm, [tm1, tm2, tm3]);

fun mk_cv_exp_load (tm1,tm2,tm3,tm4) =
  list_mk_comb (cv_exp_load_tm, [tm1, tm2, tm3, tm4]);

fun mk_cv_exp_store (tm1,tm2,tm3,tm4) =
  list_mk_comb (cv_exp_store_tm, [tm1, tm2, tm3, tm4]);


fun dest_cv_val_imm (tm:term) : term =
  dest_monop cv_val_imm_tm (ERR "dest_cv_val_imm" "not BCVVal_Imm") tm;

fun dest_cv_val_mem (tm:term) : term * term * term =
  dest_triop cv_val_mem_tm (ERR "dest_cv_val_mem" "not BCVVal_Mem") tm;

fun dest_cv_exp_const (tm:term) : term =
  dest_monop cv_exp_const_tm (ERR "dest_cv_exp_const" "not BCVExp_Const") tm;

fun dest_cv_exp_mem_const (tm:term) : (term * term * term) =
  dest_triop cv_exp_mem_const_tm (ERR "dest_cv_exp_mem_const" "not BCVExp_MemConst") tm;

fun dest_cv_exp_den (tm:term) : term  =
  dest_monop cv_exp_den_tm (ERR "dest_cv_exp_den" "not BCVExp_Den") tm;

fun dest_cv_exp_bin_exp (tm:term) : (term * term * term) =
  dest_triop cv_exp_bin_exp_tm (ERR "dest_cv_exp_bin_exp" "not BCVExp_BinExp") tm;

fun dest_cv_exp_unary_exp (tm:term) : (term * term) =
  dest_binop cv_exp_unary_exp_tm (ERR "dest_cv_exp_unary_exp" "not BCVExp_UnaryExp") tm;

fun dest_cv_exp_bin_pred (tm:term) : (term * term * term) = 
  dest_triop cv_exp_bin_pred_tm (ERR "dest_cv_exp_bin_pred" "not BCVExp_BinPred") tm;

fun dest_cv_exp_if_then_else (tm:term) : (term * term * term)  =
  dest_triop cv_exp_if_then_else_tm (ERR "dest_cv_exp_if_then_else" "not BCVExp_IfThenElse") tm;

fun dest_cv_exp_load (tm:term) : (term * term * term * term)  =
  dest_quadop cv_exp_load_tm (ERR "dest_cv_exp_load" "not BCVExp_Load") tm;

fun dest_cv_exp_store (tm:term) : (term * term * term * term)  =
  dest_quadop cv_exp_store_tm (ERR "dest_cv_exp_store" "not BCVExp_Store") tm;


fun is_cv_val_imm (tm: term) : bool = 
  can dest_cv_val_imm tm;

fun is_cv_val_mem (tm: term) : bool = 
  can dest_cv_val_mem tm;

fun is_cv_exp_const (tm: term) : bool =
  can dest_cv_exp_const tm;

fun is_cv_exp_mem_const (tm: term) : bool =
  can dest_cv_exp_mem_const tm;

fun is_cv_exp_den (tm: term) : bool =
  can dest_cv_exp_den tm;

fun is_cv_exp_bin_exp (tm: term) : bool =
  can dest_cv_exp_bin_exp tm;

fun is_cv_exp_unary_exp (tm: term) : bool =
  can dest_cv_exp_unary_exp tm;

fun is_cv_exp_bin_pred (tm: term) : bool =
  can dest_cv_exp_bin_pred tm;

fun is_cv_exp_if_then_else (tm: term) : bool =
  can dest_cv_exp_if_then_else tm;

fun is_cv_exp_load (tm: term) : bool =
  can dest_cv_exp_load tm;

fun is_cv_exp_store (tm: term) : bool =
  can dest_cv_exp_store tm;




end
