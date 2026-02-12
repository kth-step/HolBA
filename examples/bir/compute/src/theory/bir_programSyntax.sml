structure bir_programSyntax :>  bir_programSyntax =
struct

open HolKernel Parse bossLib boolLib;
open bir_programTheory;

val ERR = mk_HOL_ERR "bir_programSyntax";


(* Utilities *)

fun dest_bi_record (ty : hol_type) (err : exn) (tm: term) =
  let val (ty_rec, attributes) = TypeBase.dest_record tm;
      val _ = if ty_rec = ty then () else raise err;
  in case map snd attributes of 
      [tm1, tm2] => (tm1,tm2) 
    | _ => raise err end

fun dest_tri_record (ty : hol_type) (err : exn) (tm: term) =
  let val (ty_rec, attributes) = TypeBase.dest_record tm;
      val _ = if ty_rec = ty then () else raise err;
  in case map snd attributes of 
      [tm1, tm2, tm3] => (tm1,tm2,tm3) 
    | _ => raise err end


val le_label_tm = prim_mk_const{Name="BLE_Label", Thy="bir"};
val le_exp_tm = prim_mk_const{Name="BLE_Exp", Thy="bir"};
val stmt_assign_tm = prim_mk_const{Name="BStmt_Assign", Thy="bir"};
val stmt_jmp_tm = prim_mk_const{Name="BStmt_Jmp", Thy="bir"};
val stmt_cjmp_tm = prim_mk_const{Name="BStmt_CJmp", Thy="bir"};
val program_tm = prim_mk_const{Name="BirProgram", Thy="bir"};


fun mk_le_label tm =
  list_mk_comb (le_label_tm, [tm]);

fun mk_le_exp tm =
  list_mk_comb (le_exp_tm, [tm]);

fun mk_stmt_assign (tm1,tm2) =
  list_mk_comb (stmt_assign_tm, [tm1, tm2]);

fun mk_stmt_jmp tm =
  list_mk_comb (stmt_jmp_tm, [tm]);

fun mk_stmt_cjmp (tm1,tm2,tm3) =
  list_mk_comb (stmt_cjmp_tm, [tm1, tm2, tm3]);

fun mk_block (tm1, tm2, tm3) = 
  TypeBase.mk_record (``:bir_block_t``,
    [("bb_label",tm1), ("bb_statements", tm2), ("bb_last_statement", tm3)]);

fun mk_program tm =
  list_mk_comb (program_tm, [tm]);

fun mk_programcounter (tm1, tm2) = 
  TypeBase.mk_record (``:bir_programcounter_tm``,
    [("bpc_label",tm1), ("bpc_index", tm2)]);

fun mk_state (tm1, tm2, tm3) = 
  TypeBase.mk_record (``:bir_state_t``,
    [("bst_pc",tm1), ("bst_environ", tm2), ("bst_status", tm3)]);


  

fun dest_le_label tm = 
  dest_monop le_label_tm (ERR "dest_le_label" "not BLE_Label") tm;

fun dest_le_exp tm =
  dest_monop le_exp_tm (ERR "dest_le_exp" "not BLE_Exp") tm;

fun dest_stmt_assign tm =
  dest_binop stmt_assign_tm (ERR "dest_stmt_assign" "not BStmt_Assign") tm;

fun dest_stmt_jmp tm =
  dest_monop stmt_jmp_tm (ERR "dest_stmt_jmp" "not BStmt_Jmp") tm;

fun dest_stmt_cjmp tm =
  dest_triop stmt_cjmp_tm (ERR "dest_stmt_cjmp" "not BStmt_CJmp") tm;

fun dest_block tm =
  dest_tri_record ``:bir_block_t`` (ERR "dest_block" "not bir_block_t") tm;

fun dest_program tm =
  dest_monop program_tm (ERR "dest_program" "not BirProgram") tm;

fun dest_programcounter tm =
  dest_bi_record ``:bir_programcounter_t`` (ERR "dest_programcounter" "not bir_programcounter_t") tm;

fun dest_state tm =
  dest_tri_record ``:bir_state_t`` (ERR "dest_state" "not bir_state_t") tm;



fun is_le_label tm =
  can dest_le_label tm;

fun is_le_exp tm =
  can dest_le_exp tm;

fun is_stmt_assign tm =
  can dest_stmt_assign tm;

fun is_stmt_jmp tm =
  can dest_stmt_jmp tm;

fun is_stmt_cjmp tm =
  can dest_stmt_cjmp tm;

fun is_block tm =
  can dest_block tm;

fun is_program tm =
  can dest_program tm;

fun is_programcounter tm =
  can dest_programcounter tm;

fun is_state tm =
  can dest_state tm;



end
